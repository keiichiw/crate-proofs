#![forbid(unsafe_code)]
use bytes::Buf;
fn main() {
    for width in 1..=8 {
        let data = [0xff; 9];
        let mut be = &data[..];
        let mut checked_be = &data[..];
        let mut le = &data[..];
        let mut checked_le = &data[..];
        let mut ne = &data[..];
        let mut checked_ne = &data[..];
        let expected_checked = if width == 8 { -1 } else { ((1u64 << (8 * width)) - 1) as i64 };
        let actual = [be.get_int(width), le.get_int_le(width), ne.get_int_ne(width)];
        let checked = [checked_be.try_get_int(width), checked_le.try_get_int_le(width), checked_ne.try_get_int_ne(width)];
        assert_eq!(actual, [-1; 3]);
        for value in &checked { assert_eq!(*value, Ok(expected_checked)); }
        for rest in [be, checked_be, le, checked_le, ne, checked_ne] {
            assert_eq!(rest, &data[width..]);
        }
        println!("width={width}: get_int{{,_le,_ne}}=-1; try_get_int{{,_le,_ne}}=Ok({expected_checked}); all consumed={width}");
    }
}
