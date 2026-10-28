#![forbid(unsafe_code)]
use integer_encoding::{FixedInt, FixedIntReader, FixedIntWriter, VarIntReader};
use std::io::{Cursor,ErrorKind};
use std::panic::{catch_unwind,AssertUnwindSafe};

// A lawful sixteen-byte fixed integer. No unsafe code or malformed trait result.
#[derive(Clone,Copy,Debug,PartialEq)]
struct Fixed128(u128);
impl FixedInt for Fixed128 {
 type Bytes=[u8;16];
 fn encode_fixed(self,dst:&mut[u8])->Option<()> {
  if dst.len()!=16 {return None} dst.copy_from_slice(&self.0.to_le_bytes());Some(())
 }
 fn encode_fixed_light(self)->Self::Bytes {self.0.to_le_bytes()}
 fn decode_fixed(src:&[u8])->Option<Self> {
  if src.len()!=16 {return None} let mut a=[0;16];a.copy_from_slice(src);Some(Self(u128::from_le_bytes(a)))
 }
 fn switch_endianness(self)->Self {Self(self.0.swap_bytes())}
}
fn main() {
 let mut stream=Cursor::new([0x80,0x80,0x80,0x80,0x01,0x2a]);
 let error=stream.read_varint::<u8>().unwrap_err();
 assert_eq!(error.kind(),ErrorKind::InvalidData);assert_eq!(stream.position(),3);
 println!("width-cap: error={:?}, consumed={} of5-bytevarint, nextdecoded={}",error.kind(),stream.position(),stream.read_varint::<u8>().unwrap());
 let mut stream=Cursor::new([0xac,0x02,0x2a]);
 let error=stream.read_varint::<u8>().unwrap_err();
 assert_eq!(error.kind(),ErrorKind::UnexpectedEof);assert_eq!(stream.position(),2);
 println!("range-error: error={:?}, consumed={}, nextbyte={}",error.kind(),stream.position(),stream.read_varint::<u8>().unwrap());
 std::panic::set_hook(Box::new(|_|{}));
 let mut reader=Cursor::new([0;16]);
 let read_panic=catch_unwind(AssertUnwindSafe(||reader.read_fixedint::<Fixed128>())).is_err();
 let mut writer=Vec::<u8>::new();
 let write_panic=catch_unwind(AssertUnwindSafe(||writer.write_fixedint(Fixed128(1)))).is_err();
 assert!(read_panic&&write_panic);assert_eq!(reader.position(),0);assert!(writer.is_empty());
 println!("generic-capacity: valid16-byteFixedInt read_panics={read_panic} write_panics={write_panic} beforeI/O");
}
