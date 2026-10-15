#[cfg(creusot)]
use crate::stdlib_specs::*;
#[cfg(creusot)]
use creusot_std::prelude::*;
use std::fmt::{self, Debug, Formatter};

#[cfg_attr(creusot, ensures(match result {
    Some(pretty) => plain_options(debug_options(*f)) && pretty == (debug_options(*f).flags == 4u32),
    None => !plain_options(debug_options(*f)),
}))]
#[allow(deprecated)]
pub(crate) fn debug_mode(f: &Formatter<'_>) -> Option<bool> {
    let flags = f.flags();
    if (flags == 0 || flags == 4)
        && f.width().is_none()
        && f.precision().is_none()
        && f.align().is_none()
        && f.fill() == ' '
    {
        Some(flags == 4)
    } else {
        None
    }
}

#[cfg_attr(creusot, requires(forall<i:Int> 0 <= i && i < bytes@.len() ==> bytes@[i]@ < 128 && literal_char(bytes@[i])@ == bytes@[i]@))]
#[cfg_attr(creusot, ensures(match result {
    Ok(()) => debug_options(^f) == debug_options(*f)
        && (append_sink(*f) ==> append_sink(^f)
            && formatter_output(^f) == formatter_output(*f).concat(ascii_chars(bytes@))),
    Err(_) => true,
}))]
pub(crate) fn write_ascii(f: &mut Formatter<'_>, bytes: &[u8]) -> fmt::Result {
    let text = std::str::from_utf8(bytes).unwrap();
    #[cfg(creusot)]
    proof_assert! { text@.ext_eq(ascii_chars(bytes@)) };
    <Formatter<'_> as fmt::Write>::write_str(f, text)
}

#[cfg(creusot)]
#[logic(open, inline)]
pub fn prefix_chars(pretty: bool, first: bool) -> Seq<char> {
    if pretty {
        if first {
            seq![' ', '{', '\n'].concat(seq![' ', ' ', ' ', ' '])
        } else {
            seq![' ', ' ', ' ', ' ']
        }
    } else if first {
        seq![' ', '{', ' ']
    } else {
        seq![',', ' ']
    }
}
#[cfg(creusot)]
#[logic(open, inline)]
pub(crate) fn field_chars(
    pretty: bool,
    first: bool,
    name: Seq<char>,
    number: Seq<char>,
) -> Seq<char> {
    let body = prefix_chars(pretty, first)
        .concat(name)
        .concat(seq![':', ' '])
        .concat(number);
    if pretty {
        body.concat(seq![',', '\n'])
    } else {
        body
    }
}

#[cfg_attr(creusot, ensures(match result {
    Ok(()) => debug_options(^f) == debug_options(*f)
        && (append_sink(*f) ==> append_sink(^f)
            && formatter_output(^f) == formatter_output(*f).concat(prefix_chars(pretty, first))),
    Err(_) => true,
}))]
pub(crate) fn write_prefix(f: &mut Formatter<'_>, pretty: bool, first: bool) -> fmt::Result {
    #[cfg(creusot)]
    proof_assert! { concat_law(); true };
    #[cfg(creusot)]
    let initial = snapshot!(formatter_output(*f));
    #[cfg(creusot)]
    let sink = snapshot!(append_sink(*f));
    if pretty {
        if first {
            let open = [b' ', b'{', b'\n'];
            #[cfg(creusot)]
            proof_assert! { ascii_chars(open@).ext_eq(seq![' ', '{', '\n']) };
            write_ascii(f, &open)?;
            #[cfg(creusot)]
            proof_assert! { *sink ==> formatter_output(*f) == (*initial).concat(seq![' ', '{', '\n']) };
        }
        let spaces = [b' ', b' ', b' ', b' '];
        #[cfg(creusot)]
        proof_assert! { ascii_chars(spaces@).ext_eq(seq![' ', ' ', ' ', ' ']) };
        write_ascii(f, &spaces)?;
    } else if first {
        let open = [b' ', b'{', b' '];
        #[cfg(creusot)]
        proof_assert! { ascii_chars(open@).ext_eq(seq![' ', '{', ' ']) };
        write_ascii(f, &open)?;
    } else {
        let comma = [b',', b' '];
        #[cfg(creusot)]
        proof_assert! { ascii_chars(comma@).ext_eq(seq![',', ' ']) };
        write_ascii(f, &comma)?;
    }
    Ok(())
}

#[cfg_attr(creusot, requires(plain_options(debug_options(*f))))]
#[cfg_attr(creusot, requires(forall<i:Int> 0 <= i && i < name@.len() ==> name@[i]@ < 128 && literal_char(name@[i])@ == name@[i]@))]
#[cfg_attr(creusot, ensures(match result {
    Ok(()) => debug_options(^f) == debug_options(*f)
        && (append_sink(*f) ==> append_sink(^f)
            && formatter_output(^f) == formatter_output(*f).concat(
                field_chars(pretty, first, ascii_chars(name@), decimal_chars(value@)))),
    Err(_) => true,
}))]
pub(crate) fn write_field_u8(
    f: &mut Formatter<'_>,
    pretty: bool,
    first: bool,
    name: &[u8],
    value: u8,
) -> fmt::Result {
    #[cfg(creusot)]
    proof_assert! { concat_law(); true };
    #[cfg(creusot)]
    let initial = snapshot!(formatter_output(*f));
    #[cfg(creusot)]
    let sink = snapshot!(append_sink(*f));
    write_prefix(f, pretty, first)?;
    write_ascii(f, name)?;
    #[cfg(creusot)]
    proof_assert! { *sink ==> formatter_output(*f).ext_eq((*initial).concat(prefix_chars(pretty, first).concat(ascii_chars(name@)))) };
    write_ascii(f, &[b':', b' '])?;
    #[cfg(creusot)]
    proof_assert! { *sink ==> formatter_output(*f).ext_eq((*initial).concat(prefix_chars(pretty, first).concat(ascii_chars(name@)).concat(seq![':', ' ']))) };
    if pretty {
        write_decimal(f, value as u16)?;
    } else {
        <u8 as Debug>::fmt(&value, f)?;
    }
    #[cfg(creusot)]
    proof_assert! { *sink ==> formatter_output(*f).ext_eq((*initial).concat(prefix_chars(pretty, first).concat(ascii_chars(name@)).concat(seq![':', ' ']).concat(decimal_chars(value@)))) };
    if pretty {
        write_ascii(f, &[b',', b'\n'])?;
    }
    Ok(())
}

#[cfg_attr(creusot, requires(plain_options(debug_options(*f))))]
#[cfg_attr(creusot, requires(forall<i:Int> 0 <= i && i < name@.len() ==> name@[i]@ < 128 && literal_char(name@[i])@ == name@[i]@))]
#[cfg_attr(creusot, ensures(match result {
    Ok(()) => debug_options(^f) == debug_options(*f)
        && (append_sink(*f) ==> append_sink(^f)
            && formatter_output(^f) == formatter_output(*f).concat(
                field_chars(pretty, first, ascii_chars(name@), decimal_chars(value@)))),
    Err(_) => true,
}))]
pub(crate) fn write_field_u16(
    f: &mut Formatter<'_>,
    pretty: bool,
    first: bool,
    name: &[u8],
    value: u16,
) -> fmt::Result {
    #[cfg(creusot)]
    proof_assert! { concat_law(); true };
    #[cfg(creusot)]
    let initial = snapshot!(formatter_output(*f));
    #[cfg(creusot)]
    let sink = snapshot!(append_sink(*f));
    write_prefix(f, pretty, first)?;
    write_ascii(f, name)?;
    #[cfg(creusot)]
    proof_assert! { *sink ==> formatter_output(*f).ext_eq((*initial).concat(prefix_chars(pretty, first).concat(ascii_chars(name@)))) };
    write_ascii(f, &[b':', b' '])?;
    #[cfg(creusot)]
    proof_assert! { *sink ==> formatter_output(*f).ext_eq((*initial).concat(prefix_chars(pretty, first).concat(ascii_chars(name@)).concat(seq![':', ' ']))) };
    if pretty {
        write_decimal(f, value as u16)?;
    } else {
        <u16 as Debug>::fmt(&value, f)?;
    }
    #[cfg(creusot)]
    proof_assert! { *sink ==> formatter_output(*f).ext_eq((*initial).concat(prefix_chars(pretty, first).concat(ascii_chars(name@)).concat(seq![':', ' ']).concat(decimal_chars(value@)))) };
    if pretty {
        write_ascii(f, &[b',', b'\n'])?;
    }
    Ok(())
}

#[cfg(creusot)]
#[logic(opaque)]
#[ensures(forall<a:Seq<char>,b:Seq<char>,c:Seq<char>>
    a.concat(b).concat(c) == a.concat(b.concat(c)))]
pub(crate) fn concat_law() {
    proof_assert! { forall<a:Seq<char>,b:Seq<char>,c:Seq<char>> {
        a.concat_assoc(b,c);
        a.concat(b).concat(c) == a.concat(b.concat(c))
    }};
}

#[cfg_attr(creusot, requires(n@ < 10))]
#[cfg_attr(creusot, ensures(result@ == n@ + 48 && result@ < 128))]
#[cfg_attr(creusot, ensures(literal_char(result) == digit_char(n@) && literal_char(result)@ == result@))]
fn digit_byte(n: u16) -> u8 {
    b'0' + n as u8
}

#[cfg_attr(creusot, ensures(match result {
    Ok(()) => debug_options(^f) == debug_options(*f)
        && (append_sink(*f) ==> append_sink(^f)
            && formatter_output(^f) == formatter_output(*f).concat(decimal_chars(value@))),
    Err(_) => true,
}))]
pub(crate) fn write_decimal(f: &mut Formatter<'_>, value: u16) -> fmt::Result {
    if value < 10 {
        let buf = [digit_byte(value)];
        #[cfg(creusot)]
        proof_assert! { ascii_chars(buf@).ext_eq(decimal_chars(value@)) };
        write_ascii(f, &buf)
    } else if value < 100 {
        let buf = [digit_byte(value / 10), digit_byte((value) % 10)];
        #[cfg(creusot)]
        proof_assert! { ascii_chars(buf@).ext_eq(decimal_chars(value@)) };
        write_ascii(f, &buf)
    } else if value < 1000 {
        let buf = [
            digit_byte(value / 100),
            digit_byte((value / 10) % 10),
            digit_byte((value) % 10),
        ];
        #[cfg(creusot)]
        proof_assert! { ascii_chars(buf@).ext_eq(decimal_chars(value@)) };
        write_ascii(f, &buf)
    } else if value < 10000 {
        let buf = [
            digit_byte(value / 1000),
            digit_byte((value / 100) % 10),
            digit_byte((value / 10) % 10),
            digit_byte((value) % 10),
        ];
        #[cfg(creusot)]
        proof_assert! { ascii_chars(buf@).ext_eq(decimal_chars(value@)) };
        write_ascii(f, &buf)
    } else if true {
        let buf = [
            digit_byte(value / 10000),
            digit_byte((value / 1000) % 10),
            digit_byte((value / 100) % 10),
            digit_byte((value / 10) % 10),
            digit_byte((value) % 10),
        ];
        #[cfg(creusot)]
        proof_assert! { ascii_chars(buf@).ext_eq(decimal_chars(value@)) };
        write_ascii(f, &buf)
    } else {
        unreachable!()
    }
}
