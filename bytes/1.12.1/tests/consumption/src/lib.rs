//! Capture harness: call unchanged upstream slice Buf implementations.
use bytes::Buf;
pub fn advance_slice(mut input: &[u8], n: usize) -> &[u8] {
    <&[u8] as Buf>::advance(&mut input, n);
    input
}
pub fn copy_slice<'a>(mut input: &'a [u8], destination: &mut [u8]) -> &'a [u8] {
    <&[u8] as Buf>::copy_to_slice(&mut input, destination);
    input
}
