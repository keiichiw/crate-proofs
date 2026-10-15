//! Reviewed, conditional models for the standard-library boundaries used by
//! the public date wrappers. These contracts do not verify the std library.
#![allow(deprecated)] // Pinned Formatter::flags defines the supported Debug mode.

use std::fmt::{self, Debug, DebugStruct, DebugTuple, Formatter};
use std::hash::{Hash, Hasher};
use std::time::SystemTime;

#[cfg(creusot)]
use creusot_std::prelude::*;

/// Mathematical timestamp in nanoseconds, with an arbitrary fixed origin.
/// This opaque model is a trusted assumption about `SystemTime`.
#[cfg(creusot)]
#[trusted]
#[logic(opaque)]
pub fn time_ns(_t: SystemTime) -> Int {
    dead
}

#[cfg(creusot)]
#[logic(open, inline)]
pub fn ascii(s: Seq<char>) -> bool {
    pearlite! { forall<i: Int> 0 <= i && i < s.len() ==> s[i]@ < 128 }
}

#[cfg(creusot)]
#[logic(open, inline)]
pub fn ascii_whitespace(c: char) -> bool {
    pearlite! { c@ == 32 || (9 <= c@ && c@ <= 13) }
}

#[cfg(creusot)]
#[logic(open, inline)]
pub fn ascii_trim_relation(input: Seq<char>, output: Seq<char>) -> bool {
    pearlite! {
        exists<lo: Int, hi: Int> 0 <= lo && lo <= hi && hi <= input.len()
        && output == input.subsequence(lo, hi)
        && (forall<i: Int> 0 <= i && i < lo ==> ascii_whitespace(input[i]))
        && (forall<i: Int> hi <= i && i < input.len() ==> ascii_whitespace(input[i]))
        && (lo == hi || (!ascii_whitespace(input[lo]) && !ascii_whitespace(input[hi - 1])))
    }
}

#[cfg(creusot)]
#[logic(open, inline)]
pub fn ascii_content(chars: Seq<char>, bytes: Seq<u8>) -> bool {
    pearlite! {
        chars.len() == bytes.len()
        && (forall<i: Int> 0 <= i && i < chars.len() ==> chars[i]@ == bytes[i]@)
    }
}

#[cfg(creusot)]
extern_spec! {
    // Opaque specification avoids translating platform-private Timespec fields.
    #[ensures(time_ns(std::time::UNIX_EPOCH) == 0)]
    const std::time::UNIX_EPOCH;

    impl std::time::SystemTime {
        // Differences are restricted to values representable by Duration.
        #[requires(-18446744073709551615999999999 <= time_ns(*self) - time_ns(earlier)
            && time_ns(*self) - time_ns(earlier) <= 18446744073709551615999999999)]
        #[ensures(match result {
            Ok(d) => time_ns(*self) >= time_ns(earlier) && d@ == time_ns(*self) - time_ns(earlier),
            Err(_) => time_ns(*self) < time_ns(earlier),
        })]
        fn duration_since(&self, earlier: SystemTime) -> Result<std::time::Duration, std::time::SystemTimeError>;
    }

    mod std { mod str {
        // Restricted to ASCII; this makes no claim about non-ASCII input.
        #[requires(forall<i: Int> 0 <= i && i < v@.len() ==> v@[i]@ < 128)]
        #[ensures(match result {
            Ok(s) => s@.len() == v@.len()
                && (forall<i: Int> 0 <= i && i < v@.len() ==> s@[i]@ == v@[i]@),
            Err(_) => false,
        })]
        fn from_utf8(v: &[u8]) -> Result<&str, std::str::Utf8Error>;
    } }

    impl str {
        #[ensures(result == ascii(self@))]
        fn is_ascii(&self) -> bool;

        // `str::trim` includes vertical tab (11), unlike byte ASCII whitespace.
        #[requires(ascii(self@))]
        #[ensures(ascii(result@) && ascii_trim_relation(self@, result@))]
        fn trim(&self) -> &str;

        #[requires(ascii(self@))]
        #[ensures(ascii_content(self@, result@))]
        fn as_bytes(&self) -> &[u8];
    }
}

// Reviewed external model: 64-bit Linux and macOS arm64, supported dates only.
#[cfg(all(creusot, target_pointer_width = "64", any(target_os = "linux", all(target_os = "macos", target_arch = "aarch64"))))]
extern_spec! {
    impl std::ops::Add<std::time::Duration> for std::time::SystemTime {
        #[requires(time_ns(self) == 0 && rhs@ < 253402300800000000000)]
        #[ensures(time_ns(result) == time_ns(self) + rhs@)]
        fn add(self, rhs: std::time::Duration) -> std::time::SystemTime;
    }
}

/// Abstract sink content. Only faithful append sinks have a content guarantee.
#[trusted]
#[logic(opaque)]
pub fn formatter_output(_f: std::fmt::Formatter<'_>) -> Seq<char> {
    dead
}

/// Whether this formatter's underlying writer faithfully appends successful writes.
#[trusted]
#[logic(opaque)]
pub fn append_sink(_f: std::fmt::Formatter<'_>) -> bool {
    dead
}

extern_spec! {
    impl<'a> std::fmt::Write for std::fmt::Formatter<'a> {
        #[ensures(debug_options(^self) == debug_options(*self))]
        #[ensures(append_sink(*self) ==> append_sink(^self))]
        #[ensures(match result {
            Ok(()) => append_sink(*self) ==>
                formatter_output(^self) == formatter_output(*self).concat(data@),
            Err(_) => true,
        })]
        fn write_str(&mut self, data: &str) -> std::fmt::Result;
    }
}

// These interface lemmas are checked, not additional library assumptions.
#[logic(opaque)]
#[requires(ascii_trim_relation(s, a) && ascii_trim_relation(s, b))]
#[ensures(a == b)]
pub fn trim_unique(s: Seq<char>, a: Seq<char>, b: Seq<char>) {}

#[logic(opaque)]
#[requires(ascii_content(s, a) && ascii_content(s, b))]
#[ensures(a == b)]
pub fn bytes_unique(s: Seq<char>, a: Seq<u8>, b: Seq<u8>) {
    proof_assert! { a.ext_eq(b) };
}

// Algebraic state models for deterministic, nonpanicking hashers. State is
// sufficient internal state, not an injective/append-only history of writes.
#[trusted]
#[logic(opaque)]
pub fn supported_hasher<H: std::hash::Hasher + ?Sized>() -> bool {
    dead
}

#[trusted]
#[logic(opaque)]
pub fn hash_state<H: std::hash::Hasher + ?Sized>(_h: &H) -> Int {
    dead
}

#[trusted]
#[logic(opaque)]
pub fn hash_step_u8<H: std::hash::Hasher + ?Sized>(_state: Int, _value: u8) -> Int {
    dead
}

#[trusted]
#[logic(opaque)]
pub fn hash_step_u16<H: std::hash::Hasher + ?Sized>(_state: Int, _value: u16) -> Int {
    dead
}

#[trusted]
#[logic(opaque)]
pub fn hash_finish<H: std::hash::Hasher + ?Sized>(_state: Int) -> u64 {
    dead
}

extern_spec! {
    mod core { mod hash {
        trait Hash {
            #[requires(supported_hasher::<H>())]
            fn hash<H: Hasher>(&self, state: &mut H);
        }
        trait Hasher {
            #[requires(supported_hasher::<Self>())]
            #[ensures(result == hash_finish::<Self>(hash_state(self)))]
            fn finish(&self) -> u64;
        }
    } }

    impl std::hash::Hash for u8 {
        #[requires(supported_hasher::<H>())]
        #[ensures(hash_state(&^state) == hash_step_u8::<H>(hash_state(&*state), *self))]
        fn hash<H: std::hash::Hasher>(&self, state: &mut H);
    }
    impl std::hash::Hash for u16 {
        #[requires(supported_hasher::<H>())]
        #[ensures(hash_state(&^state) == hash_step_u16::<H>(hash_state(&*state), *self))]
        fn hash<H: std::hash::Hasher>(&self, state: &mut H);
    }
    impl std::hash::DefaultHasher {
        // Rust's constructor uses fixed keys (0, 0). Normalize that state to 0.
        #[ensures(supported_hasher::<std::hash::DefaultHasher>())]
        #[ensures(hash_state(&result) == 0)]
        fn new() -> Self;
    }
    impl std::hash::Hasher for std::hash::DefaultHasher {
        #[requires(supported_hasher::<Self>())]
        #[ensures(result == hash_finish::<Self>(hash_state(self)))]
        fn finish(&self) -> u64;
    }
}

// Restricted to direct, concrete Error payload construction, not arbitrary Into.
#[trusted]
#[logic(opaque)]
pub fn io_kind(_e: std::io::Error) -> std::io::ErrorKind {
    dead
}

#[trusted]
#[logic(opaque)]
pub fn io_payload<E>(_e: std::io::Error) -> Option<E> {
    dead
}

extern_spec! {
    impl std::io::Error {
        #[ensures(result == io_kind(*self))]
        fn kind(&self) -> std::io::ErrorKind;
        #[ensures(io_kind(result) == kind)]
        #[ensures(io_payload::<E>(result) == Some(error))]
        fn new<E: std::error::Error + Send + Sync + 'static>(kind: std::io::ErrorKind, error: E) -> std::io::Error;
    }
}

pub struct DebugOptions {
    pub flags: u32,
    pub width: Option<usize>,
    pub precision: Option<usize>,
    pub fill: char,
    pub align: Option<fmt::Alignment>,
}
#[trusted]
#[logic(opaque)]
pub fn debug_options(_f: Formatter<'_>) -> DebugOptions {
    dead
}
#[logic(open, inline)]
pub fn plain_options(o: DebugOptions) -> bool {
    pearlite! { (o.flags == 0u32 || o.flags == 4u32) && o.width == None && o.precision == None
    && o.fill == ' ' && o.align == None }
}
#[logic(open, inline)]
pub fn ascii_chars(bytes: Seq<u8>) -> Seq<char> {
    Seq::create(bytes.len(), |i| literal_char(bytes[i]))
}
#[logic(open)]
pub fn digit_char(d: Int) -> char {
    if d == 0 {
        '0'
    } else if d == 1 {
        '1'
    } else if d == 2 {
        '2'
    } else if d == 3 {
        '3'
    } else if d == 4 {
        '4'
    } else if d == 5 {
        '5'
    } else if d == 6 {
        '6'
    } else if d == 7 {
        '7'
    } else if d == 8 {
        '8'
    } else {
        '9'
    }
}
#[logic(open)]
pub fn decimal_chars(v: Int) -> Seq<char> {
    if v < 10 {
        seq![digit_char(v)]
    } else if v < 100 {
        seq![digit_char(v / 10), digit_char(v % 10)]
    } else if v < 1000 {
        seq![
            digit_char(v / 100),
            digit_char(v / 10 % 10),
            digit_char(v % 10)
        ]
    } else if v < 10000 {
        seq![
            digit_char(v / 1000),
            digit_char(v / 100 % 10),
            digit_char(v / 10 % 10),
            digit_char(v % 10)
        ]
    } else {
        seq![
            digit_char(v / 10000),
            digit_char(v / 1000 % 10),
            digit_char(v / 100 % 10),
            digit_char(v / 10 % 10),
            digit_char(v % 10)
        ]
    }
}

extern_spec! {
    impl<'a> Formatter<'a> {
        #[ensures(result == debug_options(*self).flags)]
        fn flags(&self) -> u32;
        #[ensures(result == debug_options(*self).width)]
        fn width(&self) -> Option<usize>;
        #[ensures(result == debug_options(*self).precision)]
        fn precision(&self) -> Option<usize>;
        #[ensures(result == debug_options(*self).fill)]
        fn fill(&self) -> char;
        #[ensures(result == debug_options(*self).align)]
        fn align(&self) -> Option<fmt::Alignment>;
        fn debug_struct<'b>(&'b mut self, name: &str) -> DebugStruct<'b, 'a>;
        fn debug_tuple<'b>(&'b mut self, name: &str) -> DebugTuple<'b, 'a>;
    }
    impl<'a, 'b: 'a> DebugStruct<'a, 'b> {
        fn field<'c>(&'c mut self, name: &str, value: &dyn Debug) -> &'c mut Self;
        fn finish(&mut self) -> fmt::Result;
    }
    impl<'a, 'b: 'a> DebugTuple<'a, 'b> {
        fn field<'c>(&'c mut self, value: &dyn Debug) -> &'c mut Self;
        fn finish(&mut self) -> fmt::Result;
    }
    impl Debug for u8 {
        #[ensures(match result { Ok(()) => debug_options(^f) == debug_options(*f)
            && (append_sink(*f) ==> append_sink(^f))
            && (append_sink(*f) && plain_options(debug_options(*f)) ==>
                formatter_output(^f) == formatter_output(*f).concat(decimal_chars((*self)@))), Err(_) => true })]
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result;
    }
    impl Debug for u16 {
        #[ensures(match result { Ok(()) => debug_options(^f) == debug_options(*f)
            && (append_sink(*f) ==> append_sink(^f))
            && (append_sink(*f) && plain_options(debug_options(*f)) ==>
                formatter_output(^f) == formatter_output(*f).concat(decimal_chars((*self)@))), Err(_) => true })]
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result;
    }
    impl Debug for () {
        #[ensures(match result { Ok(()) => debug_options(^f) == debug_options(*f)
            && (append_sink(*f) ==> append_sink(^f))
            && (append_sink(*f) && plain_options(debug_options(*f)) ==>
                formatter_output(^f) == formatter_output(*f).concat(seq!['(', ')'])), Err(_) => true })]
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result;
    }
}

#[logic(open)]
pub fn literal_char(b: u8) -> char {
    if b == 10u8 {
        '\n'
    } else if b == 32u8 {
        ' '
    } else if b == 123u8 {
        '{'
    } else if b == 125u8 {
        '}'
    } else if b == 40u8 {
        '('
    } else if b == 41u8 {
        ')'
    } else if b == 58u8 {
        ':'
    } else if b == 44u8 {
        ','
    } else if b == 72u8 {
        'H'
    } else if b == 116u8 {
        't'
    } else if b == 112u8 {
        'p'
    } else if b == 68u8 {
        'D'
    } else if b == 97u8 {
        'a'
    } else if b == 101u8 {
        'e'
    } else if b == 115u8 {
        's'
    } else if b == 99u8 {
        'c'
    } else if b == 109u8 {
        'm'
    } else if b == 105u8 {
        'i'
    } else if b == 110u8 {
        'n'
    } else if b == 104u8 {
        'h'
    } else if b == 111u8 {
        'o'
    } else if b == 117u8 {
        'u'
    } else if b == 114u8 {
        'r'
    } else if b == 100u8 {
        'd'
    } else if b == 121u8 {
        'y'
    } else if b == 119u8 {
        'w'
    } else if b == 69u8 {
        'E'
    } else if b == 48u8 {
        '0'
    } else if b == 49u8 {
        '1'
    } else if b == 50u8 {
        '2'
    } else if b == 51u8 {
        '3'
    } else if b == 52u8 {
        '4'
    } else if b == 53u8 {
        '5'
    } else if b == 54u8 {
        '6'
    } else if b == 55u8 {
        '7'
    } else if b == 56u8 {
        '8'
    } else if b == 57u8 {
        '9'
    } else {
        '\0'
    }
}
