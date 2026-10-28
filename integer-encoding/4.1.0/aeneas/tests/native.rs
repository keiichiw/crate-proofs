#![forbid(unsafe_code)]
use integer_encoding::{FixedInt, FixedIntReader, FixedIntWriter, VarInt, VarIntReader, VarIntWriter};
use std::io::{self, Cursor, Read, Write};
use std::panic::{catch_unwind, AssertUnwindSafe};

// Independent numeric oracle: base-128 division/remainder, not crate loops/tables.
fn unsigned_bytes(mut n: u128) -> Vec<u8> {
    let mut out = Vec::new();
    loop { let d=(n%128) as u8; n/=128; out.push(d+if n==0 {0} else {128}); if n==0 {return out} }
}
fn zigzag(n: i128) -> u128 { if n < 0 {((-n)*2-1) as u128} else {(n*2) as u128} }
fn unzigzag(n: u128) -> i128 {if n%2==0 {(n/2) as i128} else {-((n/2) as i128)-1}}
fn decode_unsigned(bytes: &[u8]) -> Option<(u128,usize)> {
    let mut n=0_u128;
    for (i,&b) in bytes.iter().take(10).enumerate() {
        n+=(b as u128%128)*128_u128.pow(i as u32);
        if b<128 {return if i<9 || b<2 {Some((n,i+1))} else {None}}
    }
    None
}
fn fixed_bytes(n: u128, count: usize) -> Vec<u8> {(0..count).map(|i| ((n/256_u128.pow(i as u32))%256) as u8).collect()}
fn corpus(bits: u32) -> Vec<u128> {
    let mask=(1_u128<<bits)-1;
    let mut xs=vec![0,1,2,mask,mask-1,mask/2,mask/2+1];
    for k in 0..bits {let p=1_u128<<k; xs.extend([p,p-1,(p+1)&mask]);}
    xs.extend(0..=255);
    let mut x=0xa0761d6478bd642f_u64;
    for _ in 0..2048 {x=x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);xs.push(x as u128&mask);}
    xs.sort_unstable();xs.dedup();xs
}
macro_rules! scalar_suite {
 ($name:ident,$t:ty,$signed:expr) => {
 #[test] fn $name() {
    let bits=<$t>::BITS; let size=std::mem::size_of::<$t>();
    assert_eq!(<$t as FixedInt>::ENCODED_SIZE,size);
    let mask=(1_u128<<bits)-1; let mut rng=0x243f6a8885a308d3_u64;
    for raw in corpus(bits) {
        let v=raw as $t;
        let n=if $signed {zigzag(v as i128)} else {v as u128};
        let expected=unsigned_bytes(n);
        assert_eq!(v.required_space(),expected.len());
        assert_eq!(v.encode_var_vec(),expected);
        let mut dst=vec![0xa5;expected.len()+5];
        assert_eq!(v.encode_var(&mut dst),expected.len());
        assert_eq!(&dst[..expected.len()],&expected);assert_eq!(&dst[expected.len()..],&[0xa5;5]);
        assert_eq!(<$t>::decode_var(&expected),Some((v,expected.len())));
        for len in 0..expected.len() {assert_eq!(<$t>::decode_var(&expected[..len]),None);}
        let mut with_tail=expected.clone();with_tail.extend([0x80,0xff,0,42]);
        assert_eq!(<$t>::decode_var(&with_tail),Some((v,expected.len())));
        if expected.len()<10 {let mut overlong=expected.clone();*overlong.last_mut().unwrap()+=128;overlong.push(0);
          assert_eq!(<$t>::decode_var(&overlong),Some((v,overlong.len())));}
        let expected_fixed=fixed_bytes(raw,size);
        assert_eq!(v.encode_fixed_light().as_ref(),expected_fixed.as_slice());
        assert_eq!(v.encode_fixed_vec(),expected_fixed);
        assert_eq!(<$t>::decode_fixed(&expected_fixed),Some(v));
        let reversed=expected_fixed.iter().fold(0_u128,|a,b|a*256+*b as u128);
        assert_eq!(v.switch_endianness(),reversed as $t);assert_eq!(v.switch_endianness().switch_endianness(),v);
        for len in 0..=size+2 {let mut dst=vec![0xa5;len];let old=dst.clone();
          let encoded=v.encode_fixed(&mut dst);
          if len==size {assert_eq!(encoded,Some(()));assert_eq!(dst,expected_fixed);} else {assert_eq!(encoded,None);assert_eq!(dst,old);}
          assert_eq!(<$t>::decode_fixed(&vec![0;len]),if len==size {Some(0 as $t)} else {None});}
        let mut cursor=Cursor::new(with_tail);assert_eq!(cursor.read_varint::<$t>().unwrap(),v);assert_eq!(cursor.position(),expected.len() as u64);
        let mut writer=ChunkWriter::new(1);assert_eq!(writer.write_varint(v).unwrap(),expected.len());assert_eq!(writer.bytes,expected);
        let mut fixed_cursor=Cursor::new(expected_fixed.clone());assert_eq!(fixed_cursor.read_fixedint::<$t>().unwrap(),v);assert_eq!(fixed_cursor.position(),size as u64);
        let mut fixed_writer=ChunkWriter::new(1);assert_eq!(fixed_writer.write_fixedint(v).unwrap(),size);assert_eq!(fixed_writer.bytes,expected_fixed);
    }
    for _ in 0..4096 {
      rng=rng.wrapping_mul(2862933555777941757).wrapping_add(3037000493);let len=(rng%14) as usize;
      let mut bytes=vec![];for _ in 0..len {rng=rng.wrapping_mul(6364136223846793005).wrapping_add(1);bytes.push((rng>>24) as u8);}
      let want=decode_unsigned(&bytes).and_then(|(n,k)| {
        if $signed {let z=unzigzag(n);let lower=-(1_i128<<(bits-1));let upper=(1_i128<<(bits-1))-1;
          if z>=lower&&z<=upper {Some((z as $t,k))} else {None}}
        else {if n<=mask {Some((n as $t,k))} else {None}}
      });
      assert_eq!(<$t>::decode_var(&bytes),want,"bytes={bytes:?}");
    }
 }
 }
}
scalar_suite!(u8_contracts,u8,false);scalar_suite!(u16_contracts,u16,false);scalar_suite!(u32_contracts,u32,false);
scalar_suite!(u64_contracts,u64,false);scalar_suite!(usize_contracts,usize,false);
scalar_suite!(i8_contracts,i8,true);scalar_suite!(i16_contracts,i16,true);scalar_suite!(i32_contracts,i32,true);
scalar_suite!(i64_contracts,i64,true);scalar_suite!(isize_contracts,isize,true);

struct ChunkWriter {bytes:Vec<u8>,chunk:usize,stop:Option<usize>,interrupt:bool}
impl ChunkWriter {fn new(chunk:usize)->Self {Self{bytes:vec![],chunk,stop:None,interrupt:false}}}
impl Write for ChunkWriter {
 fn write(&mut self,src:&[u8])->io::Result<usize> {
  if self.interrupt {self.interrupt=false;return Err(io::ErrorKind::Interrupted.into())}
  if self.stop.is_some_and(|n|self.bytes.len()>=n) {return Err(io::ErrorKind::PermissionDenied.into())}
  let available=self.stop.map_or(usize::MAX,|n|n-self.bytes.len());let n=src.len().min(self.chunk).min(available);
  self.bytes.extend_from_slice(&src[..n]);Ok(n)
 }
 fn flush(&mut self)->io::Result<()> {Ok(())}
}
struct ChunkReader {bytes:Vec<u8>,pos:usize,chunk:usize,interrupt:bool,fail_at:Option<usize>}
impl ChunkReader {fn new(bytes:Vec<u8>)->Self{Self{bytes,pos:0,chunk:1,interrupt:false,fail_at:None}}}
impl Read for ChunkReader {
 fn read(&mut self,dst:&mut[u8])->io::Result<usize> {
  if self.interrupt {self.interrupt=false;return Err(io::ErrorKind::Interrupted.into())}
  if self.fail_at.is_some_and(|n|self.pos>=n){return Err(io::ErrorKind::PermissionDenied.into())}
  let n=dst.len().min(self.chunk).min(self.bytes.len()-self.pos);dst[..n].copy_from_slice(&self.bytes[self.pos..self.pos+n]);self.pos+=n;Ok(n)
 }
}
#[test] fn malformed_varints_and_consumption() {
 assert_eq!(u64::decode_var(&[]),None);
 for n in 1..=15 {assert_eq!(u64::decode_var(&vec![0x80;n]),None);}
 for tenth in 0..=255_u8 {let mut src=vec![0x80;9];src.push(tenth);src.extend([7,8]);
  assert_eq!(u64::decode_var(&src),if tenth<2 {Some(((tenth as u64)<<63,10))} else {None});}
 let mut src=vec![0x80;9];src.push(0);assert_eq!(u8::decode_var(&src),Some((0,10)));
 let mut stream=Cursor::new(vec![0x80,0x80,0,42]);let err=stream.read_varint::<u8>().unwrap_err();
 assert_eq!(err.kind(),io::ErrorKind::InvalidData);assert_eq!(stream.position(),3);assert_eq!(stream.read_varint::<u8>().unwrap(),42);
 let mut stream=Cursor::new(vec![0xac,0x02,42]);assert_eq!(u8::decode_var(&[0xac,0x02]),None);
 assert_eq!(stream.read_varint::<u8>().unwrap_err().kind(),io::ErrorKind::UnexpectedEof);assert_eq!(stream.position(),2);assert_eq!(stream.read_varint::<u8>().unwrap(),42);
 // Width-based stream cap consumes only 3 of this 5-byte varint before error.
 let mut stream=Cursor::new(vec![0x80,0x80,0x80,0x80,1,42]);
 assert_eq!(stream.read_varint::<u8>().unwrap_err().kind(),io::ErrorKind::InvalidData);assert_eq!(stream.position(),3);
 assert_eq!(stream.read_varint::<u8>().unwrap(),128);assert_eq!(stream.position(),5);assert_eq!(stream.read_varint::<u8>().unwrap(),42);
 for src in [vec![],vec![0x80],vec![0x80;9]] {let len=src.len();let mut reader=Cursor::new(src);assert_eq!(reader.read_varint::<u64>().unwrap_err().kind(),io::ErrorKind::UnexpectedEof);assert_eq!(reader.position(),len as u64);}
 // The over-limit continuation also consumes the following byte before rejection.
 let mut reader=Cursor::new([vec![0x80;10],vec![42,9]].concat());
 assert_eq!(reader.read_varint::<u64>().unwrap_err().kind(),io::ErrorKind::InvalidData);assert_eq!(reader.position(),11);assert_eq!(reader.read_varint::<u64>().unwrap(),9);
 println!("OBSERVATION varint_stream_cap: u8 overlong zero rejected after3; long value error leaves mid-varint; u64 ten continuation bytes consume following42");
 println!("OBSERVATION varint_error_kind: complete u8 overflow300 returnsUnexpectedEof with trailing42 unread");
}
#[test] fn io_partial_eof_errors_and_writes() {
 let mut reader=ChunkReader::new(vec![1,2,3,4]);assert_eq!(reader.read_fixedint::<u32>().unwrap(),0x04030201);assert_eq!(reader.pos,4);
 let mut reader=ChunkReader::new(vec![1,2,3]);assert_eq!(reader.read_fixedint::<u32>().unwrap_err().kind(),io::ErrorKind::UnexpectedEof);assert_eq!(reader.pos,3);
 let mut reader=ChunkReader::new(vec![0xac,2]);reader.fail_at=Some(1);assert_eq!(reader.read_varint::<u64>().unwrap_err().kind(),io::ErrorKind::PermissionDenied);assert_eq!(reader.pos,1);
 let mut reader=ChunkReader::new(vec![1,2,3,4]);reader.interrupt=true;assert_eq!(reader.read_fixedint::<u32>().unwrap(),0x04030201);
 let mut reader=ChunkReader::new(vec![1]);reader.interrupt=true;assert_eq!(reader.read_varint::<u64>().unwrap_err().kind(),io::ErrorKind::Interrupted);assert_eq!(reader.pos,0);
 let mut writer=ChunkWriter::new(1);writer.interrupt=true;assert_eq!(writer.write_varint(300_u64).unwrap(),2);assert_eq!(writer.bytes,[0xac,2]);
 let mut writer=ChunkWriter::new(1);writer.stop=Some(1);assert_eq!(writer.write_varint(300_u64).unwrap_err().kind(),io::ErrorKind::PermissionDenied);assert_eq!(writer.bytes,[0xac]);
 let mut writer=ChunkWriter::new(0);assert_eq!(writer.write_varint(300_u64).unwrap_err().kind(),io::ErrorKind::WriteZero);assert!(writer.bytes.is_empty());
 let mut writer=ChunkWriter::new(1);writer.stop=Some(2);assert_eq!(writer.write_fixedint(0x04030201_u32).unwrap_err().kind(),io::ErrorKind::PermissionDenied);assert_eq!(writer.bytes,[1,2]);
}

#[derive(Copy,Clone,Debug,PartialEq)] struct WideFixed([u8;16]);
impl FixedInt for WideFixed {
 type Bytes=[u8;16];
 fn encode_fixed(self,dst:&mut[u8])->Option<()> {if dst.len()==16 {dst.copy_from_slice(&self.0);Some(())}else{None}}
 fn encode_fixed_light(self)->Self::Bytes {self.0}
 fn decode_fixed(src:&[u8])->Option<Self>{if src.len()==16 {let mut x=[0;16];x.copy_from_slice(src);Some(Self(x))}else{None}}
 fn switch_endianness(self)->Self{let mut x=self.0;x.reverse();Self(x)}
}
#[test] fn generic_fixed_stack_capacity_counterexample() {
 let mut reader=Cursor::new([0;16]);let caught=catch_unwind(AssertUnwindSafe(||reader.read_fixedint::<WideFixed>()));assert!(caught.is_err());assert_eq!(reader.position(),0);
 let mut writer=Vec::<u8>::new();let caught=catch_unwind(AssertUnwindSafe(||writer.write_fixedint(WideFixed([1;16]))));assert!(caught.is_err());assert!(writer.is_empty());
 assert_eq!(WideFixed::ENCODED_SIZE,16);assert_eq!(WideFixed([1;16]).encode_fixed_vec(),vec![1;16]);
 println!("OBSERVATION generic_fixed_stack_capacity: correct16-byteFixedInt panics in generic reader/writer beforeI/O");
}
#[test] fn insufficient_varint_destinations() {
 for n in [0_u64,127,128,16384,u64::MAX] {let space=unsigned_bytes(n as u128).len();for len in 0..space {let mut dst=vec![0xa5;len];assert!(catch_unwind(AssertUnwindSafe(||n.encode_var(&mut dst))).is_err());}}
 println!("OBSERVATION insufficient_varint_destination: panic is outside documented required-space precondition");
}
#[test] fn fixed_oversized_length_observation() {
 assert_eq!(usize::BITS,64,"native evidence records a64-bit pointer host");
 let mut dst=[0xa5;5];assert_eq!(42_u32.encode_fixed(&mut dst),None);assert_eq!(dst,[0xa5;5]);assert_eq!(u32::decode_fixed(&[42,0,0,0,99]),None);
 println!("OBSERVATION fixed_exact_length: u32 fixed encode/decode reject five-bytebuffer, bytesunchanged");
}
