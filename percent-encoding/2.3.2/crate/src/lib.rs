// Copyright 2013-2016 The rust-url developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! URLs use special characters to indicate the parts of the request.
//! For example, a `?` question mark marks the end of a path and the start of a query string.
//! In order for that character to exist inside a path, it needs to be encoded differently.
//!
//! Percent encoding replaces reserved characters with the `%` escape character
//! followed by a byte value as two hexadecimal digits.
//! For example, an ASCII space is replaced with `%20`.
//!
//! When encoding, the set of characters that can (and should, for readability) be left alone
//! depends on the context.
//! The `?` question mark mentioned above is not a separator when used literally
//! inside of a query string, and therefore does not need to be encoded.
//! The [`AsciiSet`] parameter of [`percent_encode`] and [`utf8_percent_encode`]
//! lets callers configure this.
//!
//! This crate deliberately does not provide many different sets.
//! Users should consider in what context the encoded string will be used,
//! read relevant specifications, and define their own set.
//! This is done by using the `add` method of an existing set.
//!
//! # Examples
//!
//! ```
//! use percent_encoding::{utf8_percent_encode, AsciiSet, CONTROLS};
//!
//! /// https://url.spec.whatwg.org/#fragment-percent-encode-set
//! const FRAGMENT: &AsciiSet = &CONTROLS.add(b' ').add(b'"').add(b'<').add(b'>').add(b'`');
//!
//! assert_eq!(utf8_percent_encode("foo <bar>", FRAGMENT).to_string(), "foo%20%3Cbar%3E");
//! ```
#![no_std]

// For forwards compatibility
#[cfg(feature = "std")]
extern crate std as _;

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "alloc")]
use alloc::{borrow::Cow, vec::Vec};
#[cfg(creusot)]
use core::{clone::Clone, cmp::PartialEq};
use core::{fmt, slice, str};
#[cfg(creusot)]
use creusot_std::prelude::*;
#[cfg(creusot)]
use creusot_std::std::iter::IteratorSpec;
#[cfg(creusot)]
use form_model;

pub use self::ascii_set::{AsciiSet, CONTROLS, NON_ALPHANUMERIC};

mod ascii_set;
#[cfg(creusot)]
mod encode_models;
#[cfg(creusot)]
mod encoder_bounds;
#[cfg(creusot)]
mod decoder_lemmas;
#[cfg(creusot)]
mod string_bytes_lemmas;
#[cfg(feature = "alloc")]
mod utf8_models;
#[cfg(creusot)]
mod equality_models;
mod debug_trace;
mod format_trace;
mod encoder_display;
#[cfg(feature = "alloc")]
mod encoder_cow;

#[cfg(creusot)]
#[logic(open)]
pub fn uppercase_hex(digit: Int) -> Int {
    form_model::uppercase_hex(digit)
}

#[cfg(creusot)]
#[logic(open)]
pub fn encoded_byte_model(byte: Int) -> Seq<Int> {
    Seq::singleton(37)
        .concat(Seq::singleton(uppercase_hex(byte / 16)))
        .concat(Seq::singleton(uppercase_hex(byte % 16)))
}

/// Complete byte-decoding trace used by the decoder iterator refinement.
#[cfg(creusot)]
#[logic(open)]
#[variant(input.len())]
pub fn decoded_trace(input: Seq<Int>) -> Seq<Int> {
    pearlite! {
        if input.len() == 0 {
            Seq::empty()
        } else if input.len() >= 3 && input[0] == 37
            && form_model::percent_hex_value_model(input[1]) >= 0
            && form_model::percent_hex_value_model(input[2]) >= 0
        {
            Seq::singleton(
                form_model::percent_hex_value_model(input[1]) * 16
                    + form_model::percent_hex_value_model(input[2]),
            ).concat(decoded_trace(input.subsequence(3, input.len())))
        } else {
            Seq::singleton(input[0]).concat(decoded_trace(input.subsequence(1, input.len())))
        }
    }
}

#[cfg(creusot)]
#[logic(opaque)]
#[variant(input.len())]
#[ensures(result)]
#[ensures(decoded_trace(input).len() <= input.len())]
#[ensures(input.len() <= 3 * decoded_trace(input).len())]
fn decoded_trace_length_bounds(input: Seq<Int>) -> bool {
    pearlite! {
        if input.len() == 0 {
            true
        } else if input.len() >= 3 && input[0] == 37
            && form_model::percent_hex_value_model(input[1]) >= 0
            && form_model::percent_hex_value_model(input[2]) >= 0
        {
            let tail = input.subsequence(3, input.len());
            decoded_trace_length_bounds(tail)
                && decoded_trace(input).len() == 1 + decoded_trace(tail).len()
        } else {
            let tail = input.subsequence(1, input.len());
            decoded_trace_length_bounds(tail)
                && decoded_trace(input).len() == 1 + decoded_trace(tail).len()
        }
    }
}

/// Return the percent-encoding of the given byte.
///
/// This is unconditional, unlike `percent_encode()` which has an `AsciiSet` parameter.
///
/// # Examples
///
/// ```
/// use percent_encoding::percent_encode_byte;
///
/// assert_eq!("foo bar".bytes().map(percent_encode_byte).collect::<String>(),
///            "%66%6F%6F%20%62%61%72");
/// ```
#[inline]
#[cfg_attr(creusot, ensures(form_model::byte_sequence_as_ints(result@.to_bytes())
    == encoded_byte_model(byte@)))]
pub fn percent_encode_byte(byte: u8) -> &'static str {
    let encoded = percent_encoded_bytes(byte);
    #[cfg(creusot)]
    {
        proof_assert!(form_model::ascii_three(encoded@));
        if byte != b' ' {
            proof_assert!(form_model::encoded_array_model(encoded@, byte@));
            proof_assert!(encoded_byte_model(byte@)
                == form_model::escaped_byte_chunk(byte@));
        } else {
            proof_assert!(encoded_byte_model(byte@)
                == Seq::singleton(37).concat(Seq::singleton(50)).concat(Seq::singleton(48)));
        }
        proof_assert!(form_model::byte_sequence_as_ints(encoded@) == encoded_byte_model(byte@));
    }
    // SAFETY: the numeric helper returns three ASCII bytes.
    unsafe { str::from_utf8_unchecked(encoded) }
}

#[cfg_attr(creusot, ensures(result@.len() == 3 && result[0]@ == 37 && result[1]@ == uppercase_hex(byte@ / 16) && result[2]@ == uppercase_hex(byte@ % 16) && result[0]@ < 128 && result[1]@ < 128 && result[2]@ < 128))]
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

/// Percent-encode the given bytes with the given set.
///
/// Non-ASCII bytes and bytes in `ascii_set` are encoded.
///
/// The return type:
///
/// * Implements `Iterator<Item = &str>` and therefore has a `.collect::<String>()` method,
/// * Implements `Display` and therefore has a `.to_string()` method,
/// * Implements `Into<Cow<str>>` borrowing `input` when none of its bytes are encoded.
///
/// # Examples
///
/// ```
/// use percent_encoding::{percent_encode, NON_ALPHANUMERIC};
///
/// assert_eq!(percent_encode(b"foo bar?", NON_ALPHANUMERIC).to_string(), "foo%20bar%3F");
/// ```
#[inline]
#[cfg_attr(creusot, ensures(result.remaining_input() == input@))]
#[cfg_attr(creusot, ensures(result.configured_set() == ascii_set.mask_words()))]
pub fn percent_encode<'a>(input: &'a [u8], ascii_set: &'static AsciiSet) -> PercentEncode<'a> {
    PercentEncode {
        bytes: input,
        ascii_set,
    }
}

/// Percent-encode the UTF-8 encoding of the given string.
///
/// See [`percent_encode`] regarding the return type.
///
/// # Examples
///
/// ```
/// use percent_encoding::{utf8_percent_encode, NON_ALPHANUMERIC};
///
/// assert_eq!(utf8_percent_encode("foo bar?", NON_ALPHANUMERIC).to_string(), "foo%20bar%3F");
/// ```
#[inline]
#[cfg_attr(creusot, ensures(result.remaining_input() == input@.to_bytes()))]
#[cfg_attr(creusot, ensures(result.configured_set() == ascii_set.mask_words()))]
pub fn utf8_percent_encode<'a>(input: &'a str, ascii_set: &'static AsciiSet) -> PercentEncode<'a> {
    percent_encode(input.as_bytes(), ascii_set)
}

/// The return type of [`percent_encode`] and [`utf8_percent_encode`].
pub struct PercentEncode<'a> {
    bytes: &'a [u8],
    ascii_set: &'static AsciiSet,
}

impl fmt::Debug for PercentEncode<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let struct_name = "PercentEncode";
        let bytes_field_name = "bytes";
        let set_field_name = "ascii_set";
        #[cfg(creusot)]
        let mut trace = debug_trace::DebugTrace::empty(struct_name);
        let mut builder = debug_trace::start(
            formatter,
            struct_name,
            #[cfg(creusot)]
            trace.borrow_mut(),
        );
        debug_trace::field_bytes(
            &mut builder,
            bytes_field_name,
            self.bytes,
            #[cfg(creusot)]
            trace.borrow_mut(),
        );
        debug_trace::field_ascii_set(
            &mut builder,
            set_field_name,
            self.ascii_set,
            #[cfg(creusot)]
            trace.borrow_mut(),
        );
        let result = debug_trace::finish(
            &mut builder,
            #[cfg(creusot)]
            trace.borrow_mut(),
        );
        #[cfg(creusot)]
        {
            proof_assert!(trace.struct_name == struct_name);
            proof_assert!(trace.field_names.len() == 2);
            proof_assert!(trace.field_names[0] == bytes_field_name);
            proof_assert!(trace.field_names[1] == set_field_name);
            proof_assert!(trace.field_type_tags[0] == 1u8);
            proof_assert!(trace.field_type_tags[1] == 3u8);
            proof_assert!(trace.byte_values.len() == 1);
            proof_assert!(*trace.byte_values[0] == self.bytes@);
            proof_assert!(trace.word_values.len() == 0);
            proof_assert!(trace.iter_values.len() == 0);
            proof_assert!(trace.ascii_set_values.len() == 1);
            proof_assert!(*trace.ascii_set_values[0] == self.ascii_set.mask_words());
            proof_assert!(trace.finish_status == Some(match result {
                Ok(()) => true,
                Err(_) => false,
            }));
        }
        result
    }
}

#[cfg(creusot)]
impl DeepModel for PercentEncode<'_> {
    type DeepModelTy = (Seq<u8>, Seq<u32>);

    #[logic(open(self))]
    fn deep_model(self) -> Self::DeepModelTy {
        (self.remaining_input(), self.configured_set())
    }
}

impl PartialEq for PercentEncode<'_> {
    #[cfg_attr(creusot, ensures(result == equality_models::percent_encode_eq_model(
        self.remaining_input(), self.configured_set(),
        other.remaining_input(), other.configured_set(),
    )))]
    fn eq(&self, other: &Self) -> bool {
        let bytes_equal = self.bytes == other.bytes;
        #[cfg(creusot)]
        proof_assert!(bytes_equal ==> equality_models::slice_byte_views_ext_eq_from_model(
            self.bytes, other.bytes,
        ));
        bytes_equal && self.ascii_set == other.ascii_set
    }
}

impl Eq for PercentEncode<'_> {}

impl Clone for PercentEncode<'_> {
    #[cfg_attr(creusot, ensures(result.remaining_input() == self.remaining_input()))]
    #[cfg_attr(creusot, ensures(result.configured_set() == self.configured_set()))]
    fn clone(&self) -> Self {
        Self {
            bytes: self.bytes,
            ascii_set: self.ascii_set,
        }
    }
}

impl<'a> PercentEncode<'a> {
    #[cfg(creusot)]
    #[logic(open(self), inline)]
    pub fn remaining_input(self) -> Seq<u8> {
        pearlite! { self.bytes@ }
    }

    #[cfg(creusot)]
    #[logic(open(self), inline)]
    pub fn configured_set(self) -> Seq<u32> {
        pearlite! { self.ascii_set.mask_words() }
    }
}

impl<'a> PercentEncode<'a> {
    #[cfg_attr(creusot, ensures(match result {
        None => self.remaining_input().len() == 0 && ^self == *self,
        Some(chunk) => {
            let before = self.remaining_input();
            let after = (^self).remaining_input();
            (^self).configured_set() == self.configured_set()
                && after.len() < before.len()
                && encode_models::encoded_chunks(self.configured_set(), before)
                    == Seq::singleton(form_model::string_chunk_bytes(chunk)).concat(
                        encode_models::encoded_chunks(self.configured_set(), after)
                    )
        },
    }))]
    fn next_chunk(&mut self) -> Option<&'a str> {
        let input = self.bytes;
        if input.len() == 0 {
            return None;
        }

        let first = input[0];
        if self.ascii_set.should_percent_encode(first) {
            self.bytes = &input[1..];
            let escaped = percent_encode_byte(first);
            #[cfg(creusot)]
            {
                proof_assert!(encode_models::should_encode_model(
                    self.configured_set(), first
                ));
                proof_assert!(encode_models::encoded_chunks_first_escaped(
                    self.configured_set(), input@,
                ));
            }
            Some(escaped)
        } else {
            let mut end = 0;
            #[cfg_attr(creusot, variant(input@.len() - end@))]
            #[cfg_attr(creusot, invariant(end@ <= input@.len()))]
            #[cfg_attr(creusot, invariant(pearlite! { forall<i: Int> 0 <= i && i < end@ ==> !encode_models::should_encode_model(self.configured_set(), input@[i]) }))]
            while end < input.len() && !self.ascii_set.should_percent_encode(input[end]) {
                #[cfg(creusot)]
                proof_assert!(!encode_models::should_encode_model(
                    self.configured_set(), input[end],
                ));
                #[cfg(creusot)]
                proof_assert!(encode_models::safe_prefix_extend(
                    input@, self.configured_set(), end@,
                ));
                end += 1;
            }

            let (unchanged_slice, remaining) = input.split_at(end);
            self.bytes = remaining;
            let unchanged = unsafe { str::from_utf8_unchecked(unchanged_slice) };
            #[cfg(creusot)]
            {
                proof_assert!(form_model::byte_model_subsequence(input@, 0, end@));
                proof_assert!(form_model::byte_model_subsequence(input@, end@, input@.len()));
                proof_assert!(encode_models::safe_run_end_unique(
                    input@, end@, self.configured_set(),
                ));
                proof_assert!(encode_models::encoded_chunks_first_run(
                    self.configured_set(), input@, end@,
                ));
            }
            Some(unchanged)
        }
    }
}

impl<'a> Iterator for PercentEncode<'a> {
    type Item = &'a str;

    #[cfg_attr(creusot, ensures(match result {
        Some(item) => (*self).produces(Seq::singleton(item), ^self),
        None => self.completed(),
    }))]
    #[cfg_attr(creusot, ensures((^self).configured_set() == self.configured_set()))]
    #[cfg_attr(creusot, ensures(match result {
        Some(_) => (^self).remaining_input().len() < self.remaining_input().len(),
        None => ^self == *self,
    }))]
    fn next(&mut self) -> Option<&'a str> {
        let result = self.next_chunk();
        #[cfg(creusot)]
        if let Some(item) = result {
            proof_assert!(form_model::string_chunk_singleton(item));
        }
        result
    }

    #[cfg_attr(creusot, ensures(result.0@ == if self.remaining_input().len() == 0 { 0 } else { 1 }))]
    #[cfg_attr(creusot, ensures(match result.1 { Some(upper) => upper@ == self.remaining_input().len(), None => false }))]
    #[cfg_attr(creusot, ensures(
        encode_models::encoded_chunks(self.configured_set(), self.remaining_input()).len()
            <= self.remaining_input().len()
    ))]
    #[cfg_attr(creusot, ensures(
        (self.remaining_input().len() == 0)
            == (encode_models::encoded_chunks(self.configured_set(), self.remaining_input()).len() == 0)
    ))]
    #[cfg_attr(creusot, ensures(
        self.remaining_input().len() > 0
            ==> encode_models::encoded_chunks(self.configured_set(), self.remaining_input()).len() >= 1
    ))]
    fn size_hint(&self) -> (usize, Option<usize>) {
        #[cfg(creusot)]
        proof_assert!(encoder_bounds::encoded_chunk_count_bounds(
            self.configured_set(), self.remaining_input(),
        ));
        percent_encode_size_hint(self.bytes)
    }
}

#[cfg(creusot)]
impl IteratorSpec for PercentEncode<'_> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.remaining_input().len() == 0 && resolve(self) }
    }

    #[logic(open)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            encode_models::encoded_chunks(self.configured_set(), self.remaining_input())
                == visited.map(|chunk: &str| form_model::string_chunk_bytes(chunk))
                    .concat(encode_models::encoded_chunks(o.configured_set(), o.remaining_input()))
        }
    }

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {
        let empty_chunks = Seq::<&str>::empty().map(
            |chunk: &str| form_model::string_chunk_bytes(chunk),
        );
        proof_assert!(empty_chunks.ext_eq(Seq::<Seq<Int>>::empty()));
        proof_assert!(empty_chunks == Seq::<Seq<Int>>::empty());
        let encoded = encode_models::encoded_chunks(
            self.configured_set(), self.remaining_input(),
        );
        encoded.concat_empty();
    }

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {
        proof_assert!(form_model::string_chunk_map_concat(ab, bc));
        let _ = Seq::<Seq<Int>>::concat_assoc;
    }
}

#[cfg_attr(creusot, ensures(result.0@ == if bytes@.len() == 0 { 0 } else { 1 }))]
#[cfg_attr(creusot, ensures(match result.1 { Some(upper) => upper@ == bytes@.len(), None => false }))]
fn percent_encode_size_hint(bytes: &[u8]) -> (usize, Option<usize>) {
    if bytes.len() == 0 {
        (0, Some(0))
    } else {
        (1, Some(bytes.len()))
    }
}

impl fmt::Display for PercentEncode<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        encoder_display::format_encoder(self, formatter)
    }
}

#[cfg(feature = "alloc")]
impl<'a> From<PercentEncode<'a>> for Cow<'a, str> {
    #[cfg_attr(creusot, ensures(
        encoder_cow::cow_string_bytes(result)
            == encoder_cow::flatten_chunks(encode_models::encoded_chunks(
                iter.configured_set(), iter.remaining_input()))
    ))]
    #[cfg_attr(creusot, ensures(match result {
        Cow::Borrowed(_) => encode_models::encoded_chunks(
            iter.configured_set(), iter.remaining_input()).len() <= 1,
        Cow::Owned(_) => encode_models::encoded_chunks(
            iter.configured_set(), iter.remaining_input()).len() >= 2,
    }))]
    fn from(iter: PercentEncode<'a>) -> Self {
        encoder_cow::into_cow(iter)
    }
}

/// Percent-decode the given string.
///
/// <https://url.spec.whatwg.org/#string-percent-decode>
///
/// See [`percent_decode`] regarding the return type.
#[inline]
#[cfg_attr(creusot, ensures(result.remaining_input() == input@.to_bytes()))]
pub fn percent_decode_str(input: &str) -> PercentDecode<'_> {
    percent_decode(input.as_bytes())
}

/// Percent-decode the given bytes.
///
/// <https://url.spec.whatwg.org/#percent-decode>
///
/// Any sequence of `%` followed by two hexadecimal digits is decoded.
/// The return type:
///
/// * Implements `Into<Cow<u8>>` borrowing `input` when it contains no percent-encoded sequence,
/// * Implements `Iterator<Item = u8>` and therefore has a `.collect::<Vec<u8>>()` method,
/// * Has `decode_utf8()` and `decode_utf8_lossy()` methods.
///
/// # Examples
///
/// ```
/// use percent_encoding::percent_decode;
///
/// assert_eq!(percent_decode(b"foo%20bar%3f").decode_utf8().unwrap(), "foo bar?");
/// ```
#[inline]
#[cfg_attr(creusot, ensures(result.remaining_input() == input@))]
pub fn percent_decode(input: &[u8]) -> PercentDecode<'_> {
    PercentDecode {
        bytes: input.iter(),
    }
}

/// The return type of [`percent_decode`].
pub struct PercentDecode<'a> {
    bytes: slice::Iter<'a, u8>,
}

impl fmt::Debug for PercentDecode<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let struct_name = "PercentDecode";
        let field_name = "bytes";
        #[cfg(creusot)]
        let mut trace = debug_trace::DebugTrace::empty(struct_name);
        let mut builder = debug_trace::start(
            formatter,
            struct_name,
            #[cfg(creusot)]
            trace.borrow_mut(),
        );
        debug_trace::field_byte_iter(
            &mut builder,
            field_name,
            &self.bytes,
            #[cfg(creusot)]
            trace.borrow_mut(),
        );
        let result = debug_trace::finish(
            &mut builder,
            #[cfg(creusot)]
            trace.borrow_mut(),
        );
        #[cfg(creusot)]
        {
            proof_assert!(trace.struct_name == struct_name);
            proof_assert!(trace.field_names.len() == 1);
            proof_assert!(trace.field_names[0] == field_name);
            proof_assert!(trace.field_type_tags[0] == 2u8);
            proof_assert!(trace.iter_values.len() == 1);
            proof_assert!(*trace.iter_values[0] == self.bytes@@);
            proof_assert!(trace.word_values.len() == 0);
            proof_assert!(trace.byte_values.len() == 0);
            proof_assert!(trace.ascii_set_values.len() == 0);
            proof_assert!(trace.finish_status == Some(match result {
                Ok(()) => true,
                Err(_) => false,
            }));
        }
        result
    }
}

impl Clone for PercentDecode<'_> {
    #[cfg_attr(creusot, ensures(result.remaining_input() == self.remaining_input()))]
    fn clone(&self) -> Self {
        Self {
            bytes: self.bytes.as_slice().iter(),
        }
    }
}

impl PercentDecode<'_> {
    #[cfg(creusot)]
    #[logic(open(self), inline)]
    pub fn remaining_input(self) -> Seq<u8> {
        pearlite! { self.bytes@@ }
    }
}

#[cfg_attr(creusot, ensures(match result {
    Some(value) => form_model::percent_hex_value_model(byte@) == value@,
    None => form_model::percent_hex_value_model(byte@) == -1,
}))]
fn percent_hex_value(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}

#[cfg_attr(creusot, ensures(match result {
    Some(value) => {
        let before = form_model::byte_sequence_as_ints(iter@@);
        let after = form_model::byte_sequence_as_ints((^iter)@@);
        before.len() >= 2 && form_model::percent_hex_value_model(before[0]) >= 0
            && form_model::percent_hex_value_model(before[1]) >= 0
            && value@ == form_model::percent_hex_value_model(before[0]) * 16
                + form_model::percent_hex_value_model(before[1])
            && after == before.subsequence(2, before.len())
    },
    None => (^iter)@@ == iter@@
        && (form_model::byte_sequence_as_ints(iter@@).len() < 2
            || (form_model::byte_sequence_as_ints(iter@@).len() >= 2
                && form_model::percent_hex_value_model(
                    form_model::byte_sequence_as_ints(iter@@)[0]
                ) < 0)
            || (form_model::byte_sequence_as_ints(iter@@).len() >= 2
                && form_model::percent_hex_value_model(
                    form_model::byte_sequence_as_ints(iter@@)[1]
                ) < 0)),
}))]
fn after_percent_sign(iter: &mut slice::Iter<'_, u8>) -> Option<u8> {
    let bytes = iter.as_slice();
    if bytes.len() < 2 {
        return None;
    }
    let high = percent_hex_value(bytes[0])?;
    let low = percent_hex_value(bytes[1])?;
    *iter = bytes[2..].iter();
    Some(high * 16 + low)
}

impl PercentDecode<'_> {
    #[cfg_attr(creusot, ensures(match result {
        None => self.bytes@@.len() == 0 && (^self).bytes@@ == Seq::empty()
            && ^self == *self,
        Some(value) => {
            let before = form_model::byte_sequence_as_ints(self.bytes@@);
            let after = form_model::byte_sequence_as_ints((^self).bytes@@);
            before.len() > 0
                && after.len() <= before.len()
                && (if before[0] == 37 && before.len() >= 3
                    && form_model::percent_hex_value_model(before[1]) >= 0
                    && form_model::percent_hex_value_model(before[2]) >= 0 {
                    value@ == form_model::percent_hex_value_model(before[1]) * 16
                        + form_model::percent_hex_value_model(before[2])
                        && after == before.subsequence(3, before.len())
                } else {
                    value@ == before[0]
                        && after == before.subsequence(1, before.len())
                })
        },
    }))]
    fn next_byte(&mut self) -> Option<u8> {
        let bytes = self.bytes.as_slice();
        match bytes.split_first() {
            None => None,
            Some((&byte, remaining)) => {
                #[cfg(creusot)]
                {
                    proof_assert!(form_model::byte_model_subsequence(
                        bytes@, 1, bytes@.len()
                    ));
                    proof_assert!(form_model::byte_sequence_as_ints(remaining@)
                        == form_model::byte_sequence_as_ints(bytes@)
                            .subsequence(1, bytes@.len()));
                }
                self.bytes = remaining.iter();
                #[cfg(creusot)]
                {
                    proof_assert!((self.bytes@@) == bytes@.subsequence(1, bytes@.len()));
                }
                Some(if byte == b'%' {
                    after_percent_sign(&mut self.bytes).unwrap_or(byte)
                } else {
                    byte
                })
            }
        }
    }
}

#[cfg(not(creusot))]
impl Iterator for PercentDecode<'_> {
    type Item = u8;

    fn next(&mut self) -> Option<u8> {
        self.next_byte()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        percent_decode_size_hint(self.bytes.len())
    }
}

#[cfg(creusot)]
impl Iterator for PercentDecode<'_> {
    type Item = u8;

    #[cfg_attr(creusot, ensures(match result {
        Some(item) => (*self).produces(Seq::singleton(item), ^self),
        None => self.completed(),
    }))]
    fn next(&mut self) -> Option<u8> {
        let result = self.next_byte();
        if let Some(item) = result {
            proof_assert!(form_model::byte_sequence_as_ints(Seq::singleton(item))
                .ext_eq(Seq::singleton(item@)));
        }
        result
    }

    #[cfg_attr(creusot, ensures(result.0@ == self.bytes@@.len() / 3 + if self.bytes@@.len() % 3 == 0 { 0 } else { 1 }))]
    #[cfg_attr(creusot, ensures(match result.1 { Some(upper) => upper@ == self.bytes@@.len(), None => false }))]
    #[cfg_attr(creusot, ensures(decoded_trace(form_model::byte_sequence_as_ints(self.remaining_input())).len() <= self.remaining_input().len()))]
    #[cfg_attr(creusot, ensures(self.remaining_input().len() <= 3 * decoded_trace(form_model::byte_sequence_as_ints(self.remaining_input())).len()))]
    fn size_hint(&self) -> (usize, Option<usize>) {
        #[cfg(creusot)]
        proof_assert!(decoded_trace_length_bounds(
            form_model::byte_sequence_as_ints(self.remaining_input())
        ));
        percent_decode_size_hint(self.bytes.len())
    }
}

#[cfg(creusot)]
impl IteratorSpec for PercentDecode<'_> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.remaining_input().len() == 0 && resolve(self) }
    }

    #[logic(open)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            decoded_trace(form_model::byte_sequence_as_ints(self.remaining_input()))
                == form_model::byte_sequence_as_ints(visited).concat(
                    decoded_trace(form_model::byte_sequence_as_ints(o.remaining_input()))
                )
        }
    }

    #[logic(law, prophetic)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {
        proof_assert!(
            form_model::byte_sequence_as_ints(Seq::<u8>::empty()).ext_eq(Seq::<Int>::empty())
        );
        let _ = Seq::<Int>::concat_empty;
    }

    #[logic(law, prophetic)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {
        proof_assert!(
            form_model::byte_sequence_as_ints(ab.concat(bc))
                == form_model::byte_sequence_as_ints(ab)
                    .concat(form_model::byte_sequence_as_ints(bc))
        );
        let _ = Seq::<Int>::concat_assoc;
    }
}

#[cfg_attr(creusot, ensures(result.0@ == len@ / 3 + if len@ % 3 == 0 { 0 } else { 1 }))]
#[cfg_attr(creusot, ensures(match result.1 { Some(upper) => upper@ == len@, None => false }))]
fn percent_decode_size_hint(len: usize) -> (usize, Option<usize>) {
    let lower_bound = len / 3 + if len % 3 == 0 { 0 } else { 1 };
    (lower_bound, Some(len))
}

#[cfg(feature = "alloc")]
#[cfg_attr(creusot, ensures(
    form_model::byte_sequence_as_ints((^output)@)
        == form_model::byte_sequence_as_ints(output@).concat(
            decoded_trace(form_model::byte_sequence_as_ints(iter.remaining_input()))
        )
))]
fn append_decoded(output: &mut Vec<u8>, iter: PercentDecode<'_>) {
    output.extend(iter);
}

#[cfg(feature = "alloc")]
impl<'a> From<PercentDecode<'a>> for Cow<'a, [u8]> {
    #[cfg_attr(creusot, ensures(match result {
        Cow::Borrowed(bytes) => {
            bytes@ == iter.remaining_input()
                && form_model::byte_sequence_as_ints(bytes@)
                    == decoded_trace(form_model::byte_sequence_as_ints(iter.remaining_input()))
        },
        Cow::Owned(bytes) => {
            form_model::byte_sequence_as_ints(bytes@)
                == decoded_trace(form_model::byte_sequence_as_ints(iter.remaining_input()))
                && bytes@.len() < iter.remaining_input().len()
        },
    }))]
    fn from(iter: PercentDecode<'a>) -> Self {
        match iter.if_any() {
            Some(vec) => Cow::Owned(vec),
            None => Cow::Borrowed(iter.bytes.as_slice()),
        }
    }
}

#[cfg(feature = "alloc")]
impl<'a> PercentDecode<'a> {
    /// If percent-decoding changes the bytes, return the owned decoded vector.
    #[cfg_attr(creusot, ensures(match result {
        Some(bytes) => {
            form_model::byte_sequence_as_ints(bytes@)
                == decoded_trace(form_model::byte_sequence_as_ints(self.remaining_input()))
                && bytes@.len() < self.remaining_input().len()
        },
        None => decoded_trace(form_model::byte_sequence_as_ints(self.remaining_input()))
            == form_model::byte_sequence_as_ints(self.remaining_input()),
    }))]
    fn if_any(&self) -> Option<Vec<u8>> {
        let initial_bytes = self.bytes.as_slice();
        let mut input = initial_bytes;
        let mut unchanged_bytes_len = 0;
        #[cfg_attr(creusot, variant(input@.len()))]
        #[cfg_attr(creusot, invariant(unchanged_bytes_len@ <= initial_bytes@.len()))]
        #[cfg_attr(creusot, invariant(input@ == initial_bytes@.subsequence(unchanged_bytes_len@, initial_bytes@.len())))]
        #[cfg_attr(creusot, invariant(decoded_trace(form_model::byte_sequence_as_ints(initial_bytes@)) == form_model::byte_sequence_as_ints(initial_bytes@).subsequence(0, unchanged_bytes_len@).concat(decoded_trace(form_model::byte_sequence_as_ints(input@)))))]
        while input.len() > 0 {
            let (&byte, remaining) = input.split_first().unwrap();
            if byte == b'%' {
                let mut after = remaining.iter();
                if let Some(decoded_byte) = after_percent_sign(&mut after) {
                    #[cfg(creusot)]
                    {
                        proof_assert!(decoded_trace_length_bounds(
                            form_model::byte_sequence_as_ints(after@@)
                        ));
                        proof_assert!(form_model::byte_model_subsequence(
                            initial_bytes@, unchanged_bytes_len@, initial_bytes@.len()
                        ));
                        proof_assert!(form_model::byte_model_subsequence(
                            input@, 1, input@.len()
                        ));
                        proof_assert!(form_model::byte_model_subsequence(
                            input@, 3, input@.len()
                        ));
                        proof_assert!(form_model::byte_model_subsequence(
                            remaining@, 2, remaining@.len()
                        ));
                        proof_assert!(form_model::byte_sequence_as_ints(remaining@)
                            == form_model::byte_sequence_as_ints(input@).subsequence(
                                1, form_model::byte_sequence_as_ints(input@).len()
                            ));
                        proof_assert!(form_model::byte_sequence_as_ints(after@@)
                            == form_model::byte_sequence_as_ints(remaining@).subsequence(
                                2, form_model::byte_sequence_as_ints(remaining@).len()
                            ));
                        proof_assert!(form_model::byte_sequence_as_ints(after@@)
                            == form_model::byte_sequence_as_ints(input@).subsequence(
                                3, form_model::byte_sequence_as_ints(input@).len()
                            ));
                        proof_assert!(decoder_lemmas::decoded_trace_escape_step(
                            form_model::byte_sequence_as_ints(input@),
                        ));
                        proof_assert!(decoded_byte@
                            == form_model::percent_hex_value_model(
                                form_model::byte_sequence_as_ints(input@)[1]
                            ) * 16
                                + form_model::percent_hex_value_model(
                                    form_model::byte_sequence_as_ints(input@)[2]
                                ));
                        proof_assert!(decoded_trace(form_model::byte_sequence_as_ints(input@))
                            == Seq::singleton(decoded_byte@).concat(
                                decoded_trace(form_model::byte_sequence_as_ints(after@@))
                            ));
                        proof_assert!(after@@.len() == input@.len() - 3);
                        proof_assert!({
                            form_model::byte_sequence_as_ints(initial_bytes@)
                                .subsequence(0, unchanged_bytes_len@)
                                .concat_assoc(
                                    Seq::singleton(decoded_byte@),
                                    decoded_trace(form_model::byte_sequence_as_ints(after@@)),
                                );
                            true
                        });
                    }
                    let mut decoded = initial_bytes[..unchanged_bytes_len].to_vec();
                    #[cfg(creusot)]
                    proof_assert!(form_model::byte_sequence_as_ints(decoded@)
                        == form_model::byte_sequence_as_ints(initial_bytes@)
                            .subsequence(0, unchanged_bytes_len@));
                    #[cfg(creusot)]
                    let decoded_before_push = snapshot!(decoded@);
                    decoded.push(decoded_byte);
                    #[cfg(creusot)]
                    proof_assert!(decoder_lemmas::byte_map_push_back(
                        *decoded_before_push, decoded_byte,
                    ));
                    #[cfg(creusot)]
                    proof_assert!(form_model::byte_sequence_as_ints(decoded@)
                        == form_model::byte_sequence_as_ints(initial_bytes@)
                            .subsequence(0, unchanged_bytes_len@)
                            .concat(Seq::singleton(decoded_byte@)));
                    append_decoded(&mut decoded, PercentDecode { bytes: after });
                    return Some(decoded);
                }
            }
            #[cfg(creusot)]
            {
                proof_assert!(form_model::byte_model_subsequence(input@, 1, input@.len()));
                proof_assert!(form_model::byte_sequence_as_ints(remaining@)
                    == form_model::byte_sequence_as_ints(input@).subsequence(
                        1, form_model::byte_sequence_as_ints(input@).len()
                    ));
                proof_assert!(if input@.len() >= 3 && input@[0]@ == 37 {
                    form_model::percent_hex_value_model(input@[1]@) < 0
                        || form_model::percent_hex_value_model(input@[2]@) < 0
                } else {
                    true
                });
                proof_assert!(decoder_lemmas::decoded_trace_plain_step(
                    form_model::byte_sequence_as_ints(input@),
                ));
                proof_assert!(form_model::byte_model_subsequence(
                    initial_bytes@, unchanged_bytes_len@, initial_bytes@.len()
                ));
                proof_assert!(form_model::byte_sequence_as_ints(remaining@)
                    == form_model::byte_sequence_as_ints(initial_bytes@).subsequence(
                        unchanged_bytes_len@ + 1,
                        form_model::byte_sequence_as_ints(initial_bytes@).len()
                    ));
                proof_assert!(decoder_lemmas::byte_map_nested_tail(
                    initial_bytes@, unchanged_bytes_len@,
                ));
                proof_assert!(decoded_trace(form_model::byte_sequence_as_ints(input@))
                    == Seq::singleton(byte@).concat(
                        decoded_trace(form_model::byte_sequence_as_ints(remaining@))
                    ));
                proof_assert!(decoder_lemmas::byte_map_prefix_push(
                    initial_bytes@, unchanged_bytes_len@,
                ));
                proof_assert!(form_model::byte_int_prefix_push(
                    initial_bytes@, unchanged_bytes_len@
                ));
                proof_assert!(
                    form_model::byte_sequence_as_ints(initial_bytes@)
                        .subsequence(0, unchanged_bytes_len@ + 1)
                    == form_model::byte_sequence_as_ints(initial_bytes@)
                        .subsequence(0, unchanged_bytes_len@)
                        .concat(Seq::singleton(byte@))
                );
                proof_assert!(decoder_lemmas::concat_assoc(
                    form_model::byte_sequence_as_ints(initial_bytes@)
                        .subsequence(0, unchanged_bytes_len@),
                    Seq::singleton(byte@),
                    decoded_trace(form_model::byte_sequence_as_ints(remaining@)),
                ));
            }
            unchanged_bytes_len += 1;
            #[cfg(creusot)]
            proof_assert!(form_model::byte_model_subsequence(
                initial_bytes@, unchanged_bytes_len@, initial_bytes@.len()
            ));
            input = &initial_bytes[unchanged_bytes_len..];
        }
        #[cfg(creusot)]
        {
            proof_assert!(unchanged_bytes_len@ == initial_bytes@.len());
            proof_assert!(form_model::byte_sequence_as_ints(input@).len() == 0);
            proof_assert!(form_model::byte_sequence_as_ints(initial_bytes@).subsequence(
                0, unchanged_bytes_len@,
            ) == form_model::byte_sequence_as_ints(initial_bytes@));
            proof_assert!(decoded_trace(form_model::byte_sequence_as_ints(input@)).len() == 0);
        }
        None
    }
}

#[cfg(feature = "alloc")]
impl<'a> PercentDecode<'a> {
    /// Decode the result of percent-decoding as UTF-8.
    ///
    /// This returns `Err` when the percent-decoded bytes are not well-formed in UTF-8.
    #[cfg_attr(creusot, ensures(match result {
        Ok(Cow::Borrowed(value)) => {
            let source = form_model::byte_sequence_as_ints(self.remaining_input());
            let decoded = decoded_trace(source);
            decoded == source
                && utf8_models::utf8_int_valid(decoded)
                && exists<chars: Seq<char>>
                    form_model::byte_sequence_as_ints(chars.to_bytes()) == decoded
                        && value@ == chars
        },
        Ok(Cow::Owned(value)) => {
            let source = form_model::byte_sequence_as_ints(self.remaining_input());
            let decoded = decoded_trace(source);
            decoded.len() < source.len()
                && utf8_models::utf8_int_valid(decoded)
                && exists<chars: Seq<char>>
                    form_model::byte_sequence_as_ints(chars.to_bytes()) == decoded
                        && value@ == chars
        },
        Err(error) => {
            let decoded = decoded_trace(
                form_model::byte_sequence_as_ints(self.remaining_input())
            );
            !utf8_models::utf8_int_valid(decoded)
                && utf8_models::std_error_offset(error)
                    == utf8_models::strict_error_offset(decoded)
                && utf8_models::std_error_length(error)
                    == utf8_models::strict_error_length(decoded)
        },
    }))]
    pub fn decode_utf8(self) -> Result<Cow<'a, str>, str::Utf8Error> {
        utf8_models::decode_utf8(self.into())
    }

    /// Decode the result of percent-decoding as UTF-8, lossily.
    ///
    /// Invalid UTF-8 percent-encoded byte sequences will be replaced by U+FFFD.
    #[cfg_attr(creusot, ensures({
        let source = form_model::byte_sequence_as_ints(self.remaining_input());
        let decoded = decoded_trace(source);
        let scalars = form_model::cow_str_scalars(result);
        utf8_models::lossy_int_relation(decoded, scalars)
            && (if decoded == source {
                alloc::string::String::from_utf8_lossy.postcondition((self.bytes@,), result)
            } else {
                match result {
                    Cow::Owned(_) => true,
                    Cow::Borrowed(_) => false,
                }
            })
    }))]
    pub fn decode_utf8_lossy(self) -> Cow<'a, str> {
        utf8_models::decode_utf8_lossy(self.into())
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use alloc::string::String;

    #[test]
    fn percent_encode_byte() {
        for i in 0..=0xFF {
            let encoded = super::percent_encode_byte(i);
            assert_eq!(encoded, alloc::format!("%{:02X}", i));
        }
    }

    #[test]
    fn percent_encode_accepts_ascii_set_ref() {
        let encoded = percent_encode(b"foo bar?", &AsciiSet::EMPTY);
        assert_eq!(encoded.collect::<String>(), "foo bar?");
    }

    #[test]
    fn percent_encode_collect() {
        let encoded = percent_encode(b"foo bar?", NON_ALPHANUMERIC);
        assert_eq!(encoded.collect::<String>(), String::from("foo%20bar%3F"));

        let encoded = percent_encode(b"\x00\x01\x02\x03", CONTROLS);
        assert_eq!(encoded.collect::<String>(), String::from("%00%01%02%03"));
    }

    #[test]
    fn percent_encode_display() {
        let encoded = percent_encode(b"foo bar?", NON_ALPHANUMERIC);
        assert_eq!(alloc::format!("{}", encoded), "foo%20bar%3F");
    }

    #[test]
    fn percent_encode_cow() {
        let encoded = percent_encode(b"foo bar?", NON_ALPHANUMERIC);
        assert_eq!(Cow::from(encoded), "foo%20bar%3F");
    }

    #[test]
    fn utf8_percent_encode_accepts_ascii_set_ref() {
        let encoded = super::utf8_percent_encode("foo bar?", &AsciiSet::EMPTY);
        assert_eq!(encoded.collect::<String>(), "foo bar?");
    }

    #[test]
    fn utf8_percent_encode() {
        assert_eq!(
            super::utf8_percent_encode("foo bar?", NON_ALPHANUMERIC),
            percent_encode(b"foo bar?", NON_ALPHANUMERIC)
        );
    }

    #[test]
    fn percent_decode() {
        assert_eq!(
            super::percent_decode(b"foo%20bar%3f")
                .decode_utf8()
                .unwrap(),
            "foo bar?"
        );
    }

    #[test]
    fn percent_decode_str() {
        assert_eq!(
            super::percent_decode_str("foo%20bar%3f")
                .decode_utf8()
                .unwrap(),
            "foo bar?"
        );
    }

    #[test]
    fn percent_decode_collect() {
        let decoded = super::percent_decode(b"foo%20bar%3f");
        assert_eq!(decoded.collect::<Vec<u8>>(), b"foo bar?");
    }

    #[test]
    fn percent_decode_cow() {
        let decoded = super::percent_decode(b"foo%20bar%3f");
        assert_eq!(Cow::from(decoded), Cow::Owned::<[u8]>(b"foo bar?".to_vec()));

        let decoded = super::percent_decode(b"foo bar?");
        assert_eq!(Cow::from(decoded), Cow::Borrowed(b"foo bar?"));
    }

    #[test]
    fn percent_decode_invalid_utf8() {
        // Invalid UTF-8 sequence
        let decoded = super::percent_decode(b"%00%9F%92%96")
            .decode_utf8()
            .unwrap_err();
        assert_eq!(decoded.valid_up_to(), 1);
        assert_eq!(decoded.error_len(), Some(1));
    }

    #[test]
    fn percent_decode_utf8_lossy() {
        assert_eq!(
            super::percent_decode(b"%F0%9F%92%96").decode_utf8_lossy(),
            "💖"
        );
    }

    #[test]
    fn percent_decode_utf8_lossy_invalid_utf8() {
        assert_eq!(
            super::percent_decode(b"%00%9F%92%96").decode_utf8_lossy(),
            "\u{0}���"
        );
    }
}
