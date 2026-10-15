// Copyright 2013-2016 The rust-url developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Parser and serializer for the [`application/x-www-form-urlencoded` syntax](
//! http://url.spec.whatwg.org/#application/x-www-form-urlencoded),
//! as used by HTML forms.
//!
//! Converts between a string (such as an URL’s query string)
//! and a sequence of (name, value) pairs.
#![no_std]

// For forwards compatibility
#[cfg(feature = "std")]
extern crate std as _;

extern crate alloc;

#[cfg(not(feature = "alloc"))]
compile_error!("the `alloc` feature must currently be enabled");

use alloc::borrow::{Borrow, Cow};
use alloc::string::String;
use core::str;
use percent_encoding::percent_decode;
#[cfg(creusot)]
use creusot_std::prelude::{ensures, invariant, requires, Int};

/// Convert a byte string in the `application/x-www-form-urlencoded` syntax
/// into a iterator of (name, value) pairs.
///
/// Use `parse(input.as_bytes())` to parse a `&str` string.
///
/// The names and values are percent-decoded. For instance, `%23first=%25try%25` will be
/// converted to `[("#first", "%try%")]`.
#[inline]
pub fn parse(input: &[u8]) -> Parse<'_> {
    Parse { input }
}
/// The return type of `parse()`.
#[derive(Copy, Clone)]
pub struct Parse<'a> {
    input: &'a [u8],
}

#[cfg_attr(creusot, ensures(match result {
    None => forall<i: Int> 0 <= i && i < input@.len() ==> input@[i]@ == 38,
    Some((start, eq, end, next)) => 0 <= start@ && start@ < end@ && end@ <= input@.len()
        && start@ <= eq@ && eq@ <= end@
        && (forall<i: Int> 0 <= i && i < start@ ==> input@[i]@ == 38)
        && (forall<i: Int> start@ <= i && i < end@ ==> input@[i]@ != 38)
        && (forall<i: Int> start@ <= i && i < eq@ ==> input@[i]@ != 61)
        && (eq@ < end@ ==> input@[eq@]@ == 61)
        && (end@ < input@.len() ==> input@[end@]@ == 38)
        && next@ == end@ + if end@ < input@.len() { 1 } else { 0 },
}))]
fn raw_pair_bounds(input: &[u8]) -> Option<(usize, usize, usize, usize)> {
    let mut start = 0;
    #[cfg_attr(creusot, invariant(0 <= start@ && start@ <= input@.len()
        && forall<i: Int> 0 <= i && i < start@ ==> input@[i]@ == 38))]
    while start < input.len() && input[start] == b'&' {
        start += 1;
    }
    if start == input.len() {
        return None;
    }

    let mut end = start;
    #[cfg_attr(creusot, invariant(start@ <= end@ && end@ <= input@.len()
        && forall<i: Int> start@ <= i && i < end@ ==> input@[i]@ != 38))]
    while end < input.len() && input[end] != b'&' {
        end += 1;
    }

    let mut eq = start;
    #[cfg_attr(creusot, invariant(start@ <= eq@ && eq@ <= end@
        && forall<i: Int> start@ <= i && i < eq@ ==> input@[i]@ != 61))]
    while eq < end && input[eq] != b'=' {
        eq += 1;
    }

    let next = if end < input.len() { end + 1 } else { end };
    Some((start, eq, end, next))
}

#[cfg(not(creusot))]
impl<'a> Iterator for Parse<'a> {
    type Item = (Cow<'a, str>, Cow<'a, str>);

    fn next(&mut self) -> Option<Self::Item> {
        let input = self.input;
        match raw_pair_bounds(input) {
            None => {
                self.input = &[];
                None
            }
            Some((start, eq, end, next)) => {
                self.input = &input[next..];
                let value = if eq < end { &input[eq + 1..end] } else { &[][..] };
                Some((decode(&input[start..eq]), decode(value)))
            }
        }
    }
}

fn decode(input: &[u8]) -> Cow<'_, str> {
    let replaced = replace_plus(input);
    decode_utf8_lossy(match percent_decode(&replaced).into() {
        Cow::Owned(vec) => Cow::Owned(vec),
        Cow::Borrowed(_) => replaced,
    })
}

#[cfg_attr(creusot, ensures(match result {
    Some(i) => i@ < input@.len() && input@[i@]@ == 43
        && forall<j: Int> 0 <= j && j < i@ ==> input@[j]@ != 43,
    None => forall<j: Int> 0 <= j && j < input@.len() ==> input@[j]@ != 43,
}))]
fn find_plus(input: &[u8]) -> Option<usize> {
    let mut i = 0;
    #[cfg_attr(creusot, invariant(0 <= i@ && i@ <= input@.len()
        && forall<j: Int> 0 <= j && j < i@ ==> input@[j]@ != 43))]
    while i < input.len() {
        if input[i] == b'+' {
            return Some(i);
        }
        i += 1;
    }
    None
}

#[cfg_attr(creusot, requires(first@ < bytes@.len() && bytes@[first@]@ == 43
    && forall<i: Int> 0 <= i && i < first@ ==> bytes@[i]@ != 43))]
#[cfg_attr(creusot, ensures((^bytes)@.len() == bytes@.len()
    && forall<i: Int> 0 <= i && i < bytes@.len() ==>
        (^bytes)@[i]@ == if bytes@[i]@ == 43 { 32 } else { bytes@[i]@ }))]
fn replace_plus_in_place(bytes: &mut [u8], first: usize) {
    #[cfg(creusot)]
    let original = creusot_std::prelude::snapshot!(bytes@);
    bytes[first] = b' ';
    let mut i = first + 1;
    #[cfg_attr(creusot, invariant(first@ < i@ && i@ <= bytes@.len()
        && bytes@.len() == (*original).len()
        && (forall<j: Int> 0 <= j && j < i@ ==>
            bytes@[j]@ == if (*original)[j]@ == 43 { 32 } else { (*original)[j]@ })
        && (forall<j: Int> i@ <= j && j < bytes@.len() ==> bytes@[j]@ == (*original)[j]@)))]
    while i < bytes.len() {
        if bytes[i] == b'+' {
            bytes[i] = b' ';
        }
        i += 1;
    }
}

/// Replace b'+' with b' '
fn replace_plus(input: &[u8]) -> Cow<'_, [u8]> {
    match find_plus(input) {
        None => Cow::Borrowed(input),
        Some(first_position) => {
            let mut replaced = input.to_vec();
            replace_plus_in_place(&mut replaced, first_position);
            Cow::Owned(replaced)
        }
    }
}

impl<'a> Parse<'a> {
    /// Return a new iterator that yields pairs of `String` instead of pairs of `Cow<str>`.
    pub fn into_owned(self) -> ParseIntoOwned<'a> {
        ParseIntoOwned { inner: self }
    }
}

/// Like `Parse`, but yields pairs of `String` instead of pairs of `Cow<str>`.
pub struct ParseIntoOwned<'a> {
    inner: Parse<'a>,
}

#[cfg(not(creusot))]
impl Iterator for ParseIntoOwned<'_> {
    type Item = (String, String);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
            .map(|(k, v)| (k.into_owned(), v.into_owned()))
    }
}

/// The [`application/x-www-form-urlencoded` byte serializer](
/// https://url.spec.whatwg.org/#concept-urlencoded-byte-serializer).
///
/// Return an iterator of `&str` slices.
pub fn byte_serialize(input: &[u8]) -> ByteSerialize<'_> {
    ByteSerialize { bytes: input }
}

/// Return value of `byte_serialize()`.
#[derive(Debug)]
pub struct ByteSerialize<'a> {
    bytes: &'a [u8],
}

#[cfg_attr(creusot, ensures(result == (byte@ == 42 || byte@ == 45 || byte@ == 46
    || 48 <= byte@ && byte@ <= 57 || 65 <= byte@ && byte@ <= 90 || byte@ == 95
    || 97 <= byte@ && byte@ <= 122)))]
fn byte_serialized_unchanged(byte: u8) -> bool {
    matches!(byte, b'*' | b'-' | b'.' | b'0' ..= b'9' | b'A' ..= b'Z' | b'_' | b'a' ..= b'z')
}

#[cfg_attr(creusot, ensures(result[0]@ == 37
    && result[1]@ == if byte@ / 16 < 10 { 48 + byte@ / 16 } else { 55 + byte@ / 16 }
    && result[2]@ == if byte@ % 16 < 10 { 48 + byte@ % 16 } else { 55 + byte@ % 16 }
    && result[0]@ < 128 && result[1]@ < 128 && result[2]@ < 128))]
fn percent_encoded_bytes(byte: u8) -> &'static [u8; 3] {
    match byte {
        0 => &[37, 48, 48],
        1 => &[37, 48, 49],
        2 => &[37, 48, 50],
        3 => &[37, 48, 51],
        4 => &[37, 48, 52],
        5 => &[37, 48, 53],
        6 => &[37, 48, 54],
        7 => &[37, 48, 55],
        8 => &[37, 48, 56],
        9 => &[37, 48, 57],
        10 => &[37, 48, 65],
        11 => &[37, 48, 66],
        12 => &[37, 48, 67],
        13 => &[37, 48, 68],
        14 => &[37, 48, 69],
        15 => &[37, 48, 70],
        16 => &[37, 49, 48],
        17 => &[37, 49, 49],
        18 => &[37, 49, 50],
        19 => &[37, 49, 51],
        20 => &[37, 49, 52],
        21 => &[37, 49, 53],
        22 => &[37, 49, 54],
        23 => &[37, 49, 55],
        24 => &[37, 49, 56],
        25 => &[37, 49, 57],
        26 => &[37, 49, 65],
        27 => &[37, 49, 66],
        28 => &[37, 49, 67],
        29 => &[37, 49, 68],
        30 => &[37, 49, 69],
        31 => &[37, 49, 70],
        32 => &[37, 50, 48],
        33 => &[37, 50, 49],
        34 => &[37, 50, 50],
        35 => &[37, 50, 51],
        36 => &[37, 50, 52],
        37 => &[37, 50, 53],
        38 => &[37, 50, 54],
        39 => &[37, 50, 55],
        40 => &[37, 50, 56],
        41 => &[37, 50, 57],
        42 => &[37, 50, 65],
        43 => &[37, 50, 66],
        44 => &[37, 50, 67],
        45 => &[37, 50, 68],
        46 => &[37, 50, 69],
        47 => &[37, 50, 70],
        48 => &[37, 51, 48],
        49 => &[37, 51, 49],
        50 => &[37, 51, 50],
        51 => &[37, 51, 51],
        52 => &[37, 51, 52],
        53 => &[37, 51, 53],
        54 => &[37, 51, 54],
        55 => &[37, 51, 55],
        56 => &[37, 51, 56],
        57 => &[37, 51, 57],
        58 => &[37, 51, 65],
        59 => &[37, 51, 66],
        60 => &[37, 51, 67],
        61 => &[37, 51, 68],
        62 => &[37, 51, 69],
        63 => &[37, 51, 70],
        64 => &[37, 52, 48],
        65 => &[37, 52, 49],
        66 => &[37, 52, 50],
        67 => &[37, 52, 51],
        68 => &[37, 52, 52],
        69 => &[37, 52, 53],
        70 => &[37, 52, 54],
        71 => &[37, 52, 55],
        72 => &[37, 52, 56],
        73 => &[37, 52, 57],
        74 => &[37, 52, 65],
        75 => &[37, 52, 66],
        76 => &[37, 52, 67],
        77 => &[37, 52, 68],
        78 => &[37, 52, 69],
        79 => &[37, 52, 70],
        80 => &[37, 53, 48],
        81 => &[37, 53, 49],
        82 => &[37, 53, 50],
        83 => &[37, 53, 51],
        84 => &[37, 53, 52],
        85 => &[37, 53, 53],
        86 => &[37, 53, 54],
        87 => &[37, 53, 55],
        88 => &[37, 53, 56],
        89 => &[37, 53, 57],
        90 => &[37, 53, 65],
        91 => &[37, 53, 66],
        92 => &[37, 53, 67],
        93 => &[37, 53, 68],
        94 => &[37, 53, 69],
        95 => &[37, 53, 70],
        96 => &[37, 54, 48],
        97 => &[37, 54, 49],
        98 => &[37, 54, 50],
        99 => &[37, 54, 51],
        100 => &[37, 54, 52],
        101 => &[37, 54, 53],
        102 => &[37, 54, 54],
        103 => &[37, 54, 55],
        104 => &[37, 54, 56],
        105 => &[37, 54, 57],
        106 => &[37, 54, 65],
        107 => &[37, 54, 66],
        108 => &[37, 54, 67],
        109 => &[37, 54, 68],
        110 => &[37, 54, 69],
        111 => &[37, 54, 70],
        112 => &[37, 55, 48],
        113 => &[37, 55, 49],
        114 => &[37, 55, 50],
        115 => &[37, 55, 51],
        116 => &[37, 55, 52],
        117 => &[37, 55, 53],
        118 => &[37, 55, 54],
        119 => &[37, 55, 55],
        120 => &[37, 55, 56],
        121 => &[37, 55, 57],
        122 => &[37, 55, 65],
        123 => &[37, 55, 66],
        124 => &[37, 55, 67],
        125 => &[37, 55, 68],
        126 => &[37, 55, 69],
        127 => &[37, 55, 70],
        128 => &[37, 56, 48],
        129 => &[37, 56, 49],
        130 => &[37, 56, 50],
        131 => &[37, 56, 51],
        132 => &[37, 56, 52],
        133 => &[37, 56, 53],
        134 => &[37, 56, 54],
        135 => &[37, 56, 55],
        136 => &[37, 56, 56],
        137 => &[37, 56, 57],
        138 => &[37, 56, 65],
        139 => &[37, 56, 66],
        140 => &[37, 56, 67],
        141 => &[37, 56, 68],
        142 => &[37, 56, 69],
        143 => &[37, 56, 70],
        144 => &[37, 57, 48],
        145 => &[37, 57, 49],
        146 => &[37, 57, 50],
        147 => &[37, 57, 51],
        148 => &[37, 57, 52],
        149 => &[37, 57, 53],
        150 => &[37, 57, 54],
        151 => &[37, 57, 55],
        152 => &[37, 57, 56],
        153 => &[37, 57, 57],
        154 => &[37, 57, 65],
        155 => &[37, 57, 66],
        156 => &[37, 57, 67],
        157 => &[37, 57, 68],
        158 => &[37, 57, 69],
        159 => &[37, 57, 70],
        160 => &[37, 65, 48],
        161 => &[37, 65, 49],
        162 => &[37, 65, 50],
        163 => &[37, 65, 51],
        164 => &[37, 65, 52],
        165 => &[37, 65, 53],
        166 => &[37, 65, 54],
        167 => &[37, 65, 55],
        168 => &[37, 65, 56],
        169 => &[37, 65, 57],
        170 => &[37, 65, 65],
        171 => &[37, 65, 66],
        172 => &[37, 65, 67],
        173 => &[37, 65, 68],
        174 => &[37, 65, 69],
        175 => &[37, 65, 70],
        176 => &[37, 66, 48],
        177 => &[37, 66, 49],
        178 => &[37, 66, 50],
        179 => &[37, 66, 51],
        180 => &[37, 66, 52],
        181 => &[37, 66, 53],
        182 => &[37, 66, 54],
        183 => &[37, 66, 55],
        184 => &[37, 66, 56],
        185 => &[37, 66, 57],
        186 => &[37, 66, 65],
        187 => &[37, 66, 66],
        188 => &[37, 66, 67],
        189 => &[37, 66, 68],
        190 => &[37, 66, 69],
        191 => &[37, 66, 70],
        192 => &[37, 67, 48],
        193 => &[37, 67, 49],
        194 => &[37, 67, 50],
        195 => &[37, 67, 51],
        196 => &[37, 67, 52],
        197 => &[37, 67, 53],
        198 => &[37, 67, 54],
        199 => &[37, 67, 55],
        200 => &[37, 67, 56],
        201 => &[37, 67, 57],
        202 => &[37, 67, 65],
        203 => &[37, 67, 66],
        204 => &[37, 67, 67],
        205 => &[37, 67, 68],
        206 => &[37, 67, 69],
        207 => &[37, 67, 70],
        208 => &[37, 68, 48],
        209 => &[37, 68, 49],
        210 => &[37, 68, 50],
        211 => &[37, 68, 51],
        212 => &[37, 68, 52],
        213 => &[37, 68, 53],
        214 => &[37, 68, 54],
        215 => &[37, 68, 55],
        216 => &[37, 68, 56],
        217 => &[37, 68, 57],
        218 => &[37, 68, 65],
        219 => &[37, 68, 66],
        220 => &[37, 68, 67],
        221 => &[37, 68, 68],
        222 => &[37, 68, 69],
        223 => &[37, 68, 70],
        224 => &[37, 69, 48],
        225 => &[37, 69, 49],
        226 => &[37, 69, 50],
        227 => &[37, 69, 51],
        228 => &[37, 69, 52],
        229 => &[37, 69, 53],
        230 => &[37, 69, 54],
        231 => &[37, 69, 55],
        232 => &[37, 69, 56],
        233 => &[37, 69, 57],
        234 => &[37, 69, 65],
        235 => &[37, 69, 66],
        236 => &[37, 69, 67],
        237 => &[37, 69, 68],
        238 => &[37, 69, 69],
        239 => &[37, 69, 70],
        240 => &[37, 70, 48],
        241 => &[37, 70, 49],
        242 => &[37, 70, 50],
        243 => &[37, 70, 51],
        244 => &[37, 70, 52],
        245 => &[37, 70, 53],
        246 => &[37, 70, 54],
        247 => &[37, 70, 55],
        248 => &[37, 70, 56],
        249 => &[37, 70, 57],
        250 => &[37, 70, 65],
        251 => &[37, 70, 66],
        252 => &[37, 70, 67],
        253 => &[37, 70, 68],
        254 => &[37, 70, 69],
        255 => &[37, 70, 70],
    }
}

#[cfg(not(creusot))]
impl<'a> Iterator for ByteSerialize<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        if let Some((&first, tail)) = self.bytes.split_first() {
            if !byte_serialized_unchanged(first) {
                self.bytes = tail;
                return Some(if first == b' ' {
                    "+"
                } else {
                    unsafe { str::from_utf8_unchecked(percent_encoded_bytes(first)) }
                });
            }
            let position = tail.iter().position(|&b| !byte_serialized_unchanged(b));
            let (unchanged_slice, remaining) = match position {
                // 1 for first_byte + i unchanged in tail
                Some(i) => self.bytes.split_at(1 + i),
                None => (self.bytes, &[][..]),
            };
            self.bytes = remaining;
            // This unsafe is appropriate because we have already checked these
            // bytes in byte_serialized_unchanged, which checks for a subset
            // of UTF-8. So we know these bytes are valid UTF-8, and doing
            // another UTF-8 check would be wasteful.
            Some(unsafe { str::from_utf8_unchecked(unchanged_slice) })
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.bytes.is_empty() {
            (0, Some(0))
        } else {
            (1, Some(self.bytes.len()))
        }
    }
}

/// The [`application/x-www-form-urlencoded` serializer](
/// https://url.spec.whatwg.org/#concept-urlencoded-serializer).
#[cfg(not(creusot))]
pub struct Serializer<'a, T: Target> {
    target: Option<T>,
    start_position: usize,
    encoding: EncodingOverride<'a>,
}

#[cfg(not(creusot))]
pub trait Target {
    fn as_mut_string(&mut self) -> &mut String;
    fn finish(self) -> Self::Finished;
    type Finished;
}

#[cfg(not(creusot))]
impl Target for String {
    fn as_mut_string(&mut self) -> &mut String {
        self
    }
    fn finish(self) -> Self {
        self
    }
    type Finished = Self;
}

#[cfg(not(creusot))]
impl Target for &mut String {
    fn as_mut_string(&mut self) -> &mut String {
        self
    }
    fn finish(self) -> Self {
        self
    }
    type Finished = Self;
}

#[cfg(not(creusot))]
impl<'a, T: Target> Serializer<'a, T> {
    /// Create a new `application/x-www-form-urlencoded` serializer for the given target.
    ///
    /// If the target is non-empty,
    /// its content is assumed to already be in `application/x-www-form-urlencoded` syntax.
    pub fn new(target: T) -> Self {
        Self::for_suffix(target, 0)
    }

    /// Create a new `application/x-www-form-urlencoded` serializer
    /// for a suffix of the given target.
    ///
    /// If that suffix is non-empty,
    /// its content is assumed to already be in `application/x-www-form-urlencoded` syntax.
    pub fn for_suffix(mut target: T, start_position: usize) -> Self {
        if target.as_mut_string().len() < start_position {
            panic!(
                "invalid length {} for target of length {}",
                start_position,
                target.as_mut_string().len()
            );
        }

        Serializer {
            target: Some(target),
            start_position,
            encoding: None,
        }
    }

    /// Remove any existing name/value pair.
    ///
    /// Panics if called after `.finish()`.
    pub fn clear(&mut self) -> &mut Self {
        string(&mut self.target).truncate(self.start_position);
        self
    }

    /// Set the character encoding to be used for names and values before percent-encoding.
    pub fn encoding_override(&mut self, new: EncodingOverride<'a>) -> &mut Self {
        self.encoding = new;
        self
    }

    /// Serialize and append a name/value pair.
    ///
    /// Panics if called after `.finish()`.
    pub fn append_pair(&mut self, name: &str, value: &str) -> &mut Self {
        append_pair(
            string(&mut self.target),
            self.start_position,
            self.encoding,
            name,
            value,
        );
        self
    }

    /// Serialize and append a name of parameter without any value.
    ///
    /// Panics if called after `.finish()`.
    pub fn append_key_only(&mut self, name: &str) -> &mut Self {
        append_key_only(
            string(&mut self.target),
            self.start_position,
            self.encoding,
            name,
        );
        self
    }

    /// Serialize and append a number of name/value pairs.
    ///
    /// This simply calls `append_pair` repeatedly.
    /// This can be more convenient, so the user doesn’t need to introduce a block
    /// to limit the scope of `Serializer`’s borrow of its string.
    ///
    /// Panics if called after `.finish()`.
    pub fn extend_pairs<I, K, V>(&mut self, iter: I) -> &mut Self
    where
        I: IntoIterator,
        I::Item: Borrow<(K, V)>,
        K: AsRef<str>,
        V: AsRef<str>,
    {
        {
            let string = string(&mut self.target);
            for pair in iter {
                let (k, v) = pair.borrow();
                append_pair(
                    string,
                    self.start_position,
                    self.encoding,
                    k.as_ref(),
                    v.as_ref(),
                );
            }
        }
        self
    }

    /// Serialize and append a number of names without values.
    ///
    /// This simply calls `append_key_only` repeatedly.
    /// This can be more convenient, so the user doesn’t need to introduce a block
    /// to limit the scope of `Serializer`’s borrow of its string.
    ///
    /// Panics if called after `.finish()`.
    pub fn extend_keys_only<I, K>(&mut self, iter: I) -> &mut Self
    where
        I: IntoIterator,
        I::Item: Borrow<K>,
        K: AsRef<str>,
    {
        {
            let string = string(&mut self.target);
            for key in iter {
                let k = key.borrow().as_ref();
                append_key_only(string, self.start_position, self.encoding, k);
            }
        }
        self
    }

    /// If this serializer was constructed with a string, take and return that string.
    ///
    /// ```rust
    /// use form_urlencoded;
    /// let encoded: String = form_urlencoded::Serializer::new(String::new())
    ///     .append_pair("foo", "bar & baz")
    ///     .append_pair("saison", "Été+hiver")
    ///     .finish();
    /// assert_eq!(encoded, "foo=bar+%26+baz&saison=%C3%89t%C3%A9%2Bhiver");
    /// ```
    ///
    /// Panics if called more than once.
    pub fn finish(&mut self) -> T::Finished {
        self.target
            .take()
            .expect("url::form_urlencoded::Serializer double finish")
            .finish()
    }
}

#[cfg(not(creusot))]
fn append_separator_if_needed(string: &mut String, start_position: usize) {
    if string.len() > start_position {
        string.push('&')
    }
}

#[cfg(not(creusot))]
fn string<T: Target>(target: &mut Option<T>) -> &mut String {
    target
        .as_mut()
        .expect("url::form_urlencoded::Serializer finished")
        .as_mut_string()
}

#[cfg(not(creusot))]
fn append_pair(
    string: &mut String,
    start_position: usize,
    encoding: EncodingOverride<'_>,
    name: &str,
    value: &str,
) {
    append_separator_if_needed(string, start_position);
    append_encoded(name, string, encoding);
    string.push('=');
    append_encoded(value, string, encoding);
}

#[cfg(not(creusot))]
fn append_key_only(
    string: &mut String,
    start_position: usize,
    encoding: EncodingOverride,
    name: &str,
) {
    append_separator_if_needed(string, start_position);
    append_encoded(name, string, encoding);
}

#[cfg(not(creusot))]
fn append_encoded(s: &str, string: &mut String, encoding: EncodingOverride<'_>) {
    string.extend(byte_serialize(&encode(encoding, s)))
}

#[cfg(not(creusot))]
pub(crate) fn encode<'a>(encoding_override: EncodingOverride<'_>, input: &'a str) -> Cow<'a, [u8]> {
    if let Some(o) = encoding_override {
        return o(input);
    }
    input.as_bytes().into()
}

// std::ptr::addr_eq was stabilized in rust 1.76. Once we upgrade
// the MSRV we can remove this lint override.
#[allow(ambiguous_wide_pointer_comparisons)]
pub(crate) fn decode_utf8_lossy(input: Cow<'_, [u8]>) -> Cow<'_, str> {
    // Note: This function is duplicated in `percent_encoding/lib.rs`.
    match input {
        Cow::Borrowed(bytes) => String::from_utf8_lossy(bytes),
        Cow::Owned(bytes) => {
            match String::from_utf8_lossy(&bytes) {
                Cow::Borrowed(utf8) => {
                    // If from_utf8_lossy returns a Cow::Borrowed, then we can
                    // be sure our original bytes were valid UTF-8. This is because
                    // if the bytes were invalid UTF-8 from_utf8_lossy would have
                    // to allocate a new owned string to back the Cow so it could
                    // replace invalid bytes with a placeholder.

                    // First we do a debug_assert to confirm our description above.
                    let raw_utf8: *const [u8] = utf8.as_bytes();
                    debug_assert!(core::ptr::eq(raw_utf8, &*bytes));

                    // Given we know the original input bytes are valid UTF-8,
                    // and we have ownership of those bytes, we re-use them and
                    // return a Cow::Owned here.
                    Cow::Owned(unsafe { String::from_utf8_unchecked(bytes) })
                }
                Cow::Owned(s) => Cow::Owned(s),
            }
        }
    }
}

#[cfg(not(creusot))]
pub type EncodingOverride<'a> = Option<&'a dyn Fn(&str) -> Cow<'_, [u8]>>;
