use bytes::Buf;
use std::io::Cursor;
pub fn remaining(x: &Cursor<&[u8]>) -> usize { <Cursor<&[u8]> as Buf>::remaining(x) }
pub fn chunk<'a>(x: &'a Cursor<&[u8]>) -> &'a [u8] { <Cursor<&[u8]> as Buf>::chunk(x) }
pub fn advance(x: &mut Cursor<&[u8]>,n:usize) { <Cursor<&[u8]> as Buf>::advance(x,n) }
