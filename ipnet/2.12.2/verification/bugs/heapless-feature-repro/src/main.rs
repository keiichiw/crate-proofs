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
#[derive(Debug)] struct E;
impl std::fmt::Display for E { fn fmt(&self,f:&mut std::fmt::Formatter<'_>)->std::fmt::Result { f.write_str("unsupported") } }
impl std::error::Error for E {}
impl serde::ser::Error for E { fn custom<T: std::fmt::Display>(_:T)->Self { E } }
struct Sink;
macro_rules! unsupported_scalar { ($($n:ident:$t:ty),*) => {$ (fn $n(self,_:$t)->Result<usize,E>{Err(E)})*}; }
impl Serializer for Sink {
    type Ok=usize; type Error=E;
    type SerializeSeq=Impossible<usize,E>; type SerializeTuple=Impossible<usize,E>;
    type SerializeTupleStruct=Impossible<usize,E>; type SerializeTupleVariant=Impossible<usize,E>;
    type SerializeMap=Impossible<usize,E>; type SerializeStruct=Impossible<usize,E>;
    type SerializeStructVariant=Impossible<usize,E>;
    unsupported_scalar!(serialize_bool:bool,serialize_i8:i8,serialize_i16:i16,serialize_i32:i32,serialize_i64:i64,serialize_u8:u8,serialize_u16:u16,serialize_u32:u32,serialize_u64:u64,serialize_f32:f32,serialize_f64:f64,serialize_char:char);
    fn serialize_str(self,v:&str)->Result<usize,E>{ assert_eq!(v,"255.255.255.255/32"); Ok(v.len()) }
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
    // Intentionally retain serde's default collect_str, which calls to_string().
}
fn main(){
    let n:ipnet::Ipv4Net="255.255.255.255/32".parse().unwrap();
    ALLOCS.store(0,Ordering::SeqCst);
    let len=n.serialize(Sink).unwrap();
    let allocations=ALLOCS.load(Ordering::SeqCst);
    println!("heapless={} legacy={} bytes={} allocations={}",cfg!(feature="heapless"),cfg!(feature="legacy"),len,allocations);
    if cfg!(feature="legacy") {assert_eq!(allocations,0);} else {assert!(allocations>0);}
}
