#![forbid(unsafe_code)]
use bytes::Buf;
fn main() {
    let mut input = &[0xff_u8][..];
    assert_eq!(input.try_get_int(1), Ok(-1));
}
