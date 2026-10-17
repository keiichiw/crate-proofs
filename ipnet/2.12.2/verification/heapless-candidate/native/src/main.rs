use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};
use serde::{Serialize, Serializer};
use serde::ser::Impossible;
static ALLOCS: AtomicUsize = AtomicUsize::new(0);
struct Counting;
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 { ALLOCS.fetch_add(1, Ordering::SeqCst); System.alloc(l) }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) { System.dealloc(p,l) }
    unsafe fn realloc(&self,p:*mut u8,l:Layout,n:usize)->*mut u8 { ALLOCS.fetch_add(1,Ordering::SeqCst); System.realloc(p,l,n) }
}
#[global_allocator] static ALLOCATOR: Counting = Counting;
#[derive(Debug, PartialEq, Eq)] struct E;
impl std::fmt::Display for E { fn fmt(&self,f:&mut std::fmt::Formatter<'_>)->std::fmt::Result { f.write_str("unsupported") } }
impl std::error::Error for E {}
impl serde::ser::Error for E { fn custom<T: std::fmt::Display>(_:T)->Self { E } }
struct Sink<'a> { expected: &'a str, fail: bool, queries: &'a std::cell::Cell<usize> }
macro_rules! unsupported_scalar { ($($n:ident:$t:ty),*) => {$ (fn $n(self,_:$t)->Result<usize,E>{Err(E)})*}; }
impl Serializer for Sink<'_> {
    type Ok=usize; type Error=E;
    type SerializeSeq=Impossible<usize,E>; type SerializeTuple=Impossible<usize,E>;
    type SerializeTupleStruct=Impossible<usize,E>; type SerializeTupleVariant=Impossible<usize,E>;
    type SerializeMap=Impossible<usize,E>; type SerializeStruct=Impossible<usize,E>;
    type SerializeStructVariant=Impossible<usize,E>;
    unsupported_scalar!(serialize_bool:bool,serialize_i8:i8,serialize_i16:i16,serialize_i32:i32,serialize_i64:i64,serialize_u8:u8,serialize_u16:u16,serialize_u32:u32,serialize_u64:u64,serialize_f32:f32,serialize_f64:f64,serialize_char:char);
    fn serialize_str(self,v:&str)->Result<usize,E>{ assert_eq!(v,self.expected); if self.fail { Err(E) } else { Ok(v.len()) } }
    fn serialize_bytes(self,_:&[u8])->Result<usize,E>{Err(E)}
    fn serialize_none(self)->Result<usize,E>{Err(E)}
    fn serialize_some<T:?Sized+Serialize>(self,_:&T)->Result<usize,E>{Err(E)}
    fn serialize_unit(self)->Result<usize,E>{Err(E)}
    fn serialize_unit_struct(self,_:&'static str)->Result<usize,E>{Err(E)}
    fn serialize_unit_variant(self,_:&'static str,_:u32,_:&'static str)->Result<usize,E>{Err(E)}
    fn serialize_newtype_struct<T:?Sized+Serialize>(self,_:&'static str,_:&T)->Result<usize,E>{Err(E)}
    fn serialize_newtype_variant<T:?Sized+Serialize>(self,_:&'static str,_:u32,_:&'static str,_:&T)->Result<usize,E>{Err(E)}
    fn serialize_seq(self,_:Option<usize>)->Result<Self::SerializeSeq,E>{Err(E)}
    fn serialize_tuple(self,_:usize)->Result<Self::SerializeTuple,E>{Err(E)}
    fn serialize_tuple_struct(self,_:&'static str,_:usize)->Result<Self::SerializeTupleStruct,E>{Err(E)}
    fn serialize_tuple_variant(self,_:&'static str,_:u32,_:&'static str,_:usize)->Result<Self::SerializeTupleVariant,E>{Err(E)}
    fn serialize_map(self,_:Option<usize>)->Result<Self::SerializeMap,E>{Err(E)}
    fn serialize_struct(self,_:&'static str,_:usize)->Result<Self::SerializeStruct,E>{Err(E)}
    fn serialize_struct_variant(self,_:&'static str,_:u32,_:&'static str,_:usize)->Result<Self::SerializeStructVariant,E>{Err(E)}
    fn is_human_readable(&self) -> bool { self.queries.set(self.queries.get() + 1); true }
    // Keep default collect_str to make the serde-only allocation control observable.
}

fn exercise<T: Serialize + std::fmt::Display>(n: &T, capacity: usize, query_count: usize) -> usize {
    let expected = n.to_string();
    assert!(expected.len() <= capacity);
    for fail in [false, true] {
        let queries = std::cell::Cell::new(0);
        ALLOCS.store(0, Ordering::SeqCst);
        let result = n.serialize(Sink { expected: &expected, fail, queries: &queries });
        let allocations = ALLOCS.load(Ordering::SeqCst);
        assert_eq!(queries.get(), query_count);
        assert_eq!(result, if fail { Err(E) } else { Ok(expected.len()) });
        if cfg!(any(feature="heapless", feature="legacy")) {
            assert_eq!(allocations, 0, "temporary allocation for {expected}");
        } else {
            assert!(allocations > 0, "serde-only positive allocation control");
        }
    }
    2
}
fn main() {
    let mut cases = 0;
    let v4 = [0, 1, 0xff, 0x01020304, 0x7fffffff, 0x80000000, 0xfffffffe, u32::MAX];
    for bits in v4 {
        for p in 0..=32 {
            let n = ipnet::Ipv4Net::new(std::net::Ipv4Addr::from(bits), p).unwrap();
            cases += exercise(&n, 18, 1);
            cases += exercise(&ipnet::IpNet::V4(n), 18, 2);
        }
    }
    let v6 = [0, 1, 0xffff, 0x00000000000000000000ffffc0000201,
        0x0102030405060708090a0b0c0d0e0f10, 0xffff000000000000000000000000ffff,
        0x20010db8000000000000000000000001, 1u128 << 127, u128::MAX-1, u128::MAX];
    for bits in v6 {
        for p in 0..=128 {
            let n = ipnet::Ipv6Net::new(std::net::Ipv6Addr::from(bits), p).unwrap();
            cases += exercise(&n, 43, 1);
            cases += exercise(&ipnet::IpNet::V6(n), 43, 2);
        }
    }
    println!("PASS cases={cases} std={} heapless={} legacy={} serde_only={}",
        cfg!(feature="std"), cfg!(feature="heapless"), cfg!(feature="legacy"), cfg!(feature="serde-only"));
}
