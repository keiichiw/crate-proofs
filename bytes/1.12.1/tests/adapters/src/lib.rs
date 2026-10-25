use bytes::{Buf,buf::{Take,Chain,IntoIter}};
pub fn take_remaining<T:Buf>(x:&Take<T>)->usize { <Take<T> as Buf>::remaining(x) }
pub fn take_chunk<T:Buf>(x:&Take<T>)->&[u8] { <Take<T> as Buf>::chunk(x) }
pub fn take_advance<T:Buf>(x:&mut Take<T>,n:usize) { <Take<T> as Buf>::advance(x,n) }
pub fn chain_remaining<T:Buf,U:Buf>(x:&Chain<T,U>)->usize { <Chain<T,U> as Buf>::remaining(x) }
pub fn chain_chunk<T:Buf,U:Buf>(x:&Chain<T,U>)->&[u8] { <Chain<T,U> as Buf>::chunk(x) }
pub fn chain_advance<T:Buf,U:Buf>(x:&mut Chain<T,U>,n:usize) { <Chain<T,U> as Buf>::advance(x,n) }
pub fn next<T:Buf>(x:&mut IntoIter<T>)->Option<u8> { x.next() }
pub fn slice_remaining(x:&&[u8])->usize { <&[u8] as Buf>::remaining(x) }
pub fn slice_chunk<'a>(x:&'a &[u8])->&'a[u8] { <&[u8] as Buf>::chunk(x) }
pub fn slice_has_remaining(x:&&[u8])->bool { <&[u8] as Buf>::has_remaining(x) }
pub fn slice_advance(mut x:&[u8],n:usize)->&[u8] { <&[u8] as Buf>::advance(&mut x,n); x }
pub fn size_hint<T:Buf>(x:&IntoIter<T>)->(usize,Option<usize>) { x.size_hint() }

pub fn take_has_remaining<T:Buf>(x:&Take<T>)->bool { x.has_remaining() }
pub fn chain_has_remaining<T:Buf,U:Buf>(x:&Chain<T,U>)->bool { x.has_remaining() }
pub fn concrete_take_remaining(x:&Take<&[u8]>)->usize { x.remaining() }
pub fn concrete_take_chunk<'a>(x:&'a Take<&[u8]>)->&'a[u8] { x.chunk() }
pub fn concrete_take_advance(x:&mut Take<&[u8]>,n:usize) { x.advance(n) }
pub fn concrete_chain_remaining(x:&Chain<&[u8],&[u8]>)->usize { x.remaining() }
pub fn concrete_chain_chunk<'a>(x:&'a Chain<&[u8],&[u8]>)->&'a[u8] { x.chunk() }
pub fn concrete_chain_advance(x:&mut Chain<&[u8],&[u8]>,n:usize) { x.advance(n) }
pub fn concrete_take_take_advance(x:&mut Take<Take<&[u8]>>,n:usize) { x.advance(n) }
pub fn concrete_take_chain_advance(x:&mut Take<Chain<&[u8],&[u8]>>,n:usize) { x.advance(n) }
