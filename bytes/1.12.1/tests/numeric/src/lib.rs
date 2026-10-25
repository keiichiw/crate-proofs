use bytes::Buf;
pub fn read_i8(mut input: &[u8]) -> (i8, &[u8]) {
    let out = <&[u8] as Buf>::get_i8(&mut input);
    (out, input)
}
pub fn try_read_i8(mut input: &[u8]) -> (Result<i8, bytes::TryGetError>, &[u8]) {
    let out = <&[u8] as Buf>::try_get_i8(&mut input);
    (out, input)
}
pub fn read_u8(mut input: &[u8]) -> (u8, &[u8]) {
    let out = <&[u8] as Buf>::get_u8(&mut input);
    (out, input)
}
pub fn try_read_u8(mut input: &[u8]) -> (Result<u8, bytes::TryGetError>, &[u8]) {
    let out = <&[u8] as Buf>::try_get_u8(&mut input);
    (out, input)
}
pub fn force_slice_dictionary(x: &bytes::buf::Take<&[u8]>) -> usize {
    <bytes::buf::Take<&[u8]> as Buf>::remaining(x)
}
