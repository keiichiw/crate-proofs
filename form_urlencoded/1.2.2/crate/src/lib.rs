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

use alloc::borrow::{Cow, ToOwned};
#[cfg(not(creusot))]
use alloc::borrow::Borrow;
use alloc::string::String;
use alloc::vec::Vec;
use core::str;
#[cfg(creusot)]
use creusot_std::prelude::*;
#[cfg(creusot)]
mod plus_model;
#[cfg(creusot)]
use plus_model::{no_plus_identity, plus_result_exact, replace_plus_model};
#[cfg(creusot)]
mod ownership_model;
#[cfg(creusot)]
mod stdlib_models;

/// Convert a byte string in the `application/x-www-form-urlencoded` syntax
/// into a iterator of (name, value) pairs.
///
/// Use `parse(input.as_bytes())` to parse a `&str` string.
///
/// The names and values are percent-decoded. For instance, `%23first=%25try%25` will be
/// converted to `[("#first", "%try%")]`.
#[inline]
#[cfg_attr(creusot, ensures(result.remaining_input() == input@))]
pub fn parse(input: &[u8]) -> Parse<'_> {
    Parse { input }
}
/// The return type of `parse()`.
#[derive(Copy)]
pub struct Parse<'a> {
    input: &'a [u8],
}

impl Parse<'_> {
    #[cfg(creusot)]
    #[logic(open(self), inline)]
    pub fn remaining_input(self) -> Seq<u8> {
        pearlite! { self.input@ }
    }
}

impl Clone for Parse<'_> {
    #[cfg_attr(creusot, ensures(result.remaining_input() == self.remaining_input()))]
    fn clone(&self) -> Self {
        Self { input: self.input }
    }
}

#[cfg_attr(creusot, ensures(match result {
    None => forall<i: Int> 0 <= i && i < input@.len() ==> input@[i]@ == 38,
    Some((start, eq, end, next)) => 0 <= start@ && start@ < end@ && end@ <= input@.len()
        && start@ == skip_ampersands(input@, 0)
        && start@ <= eq@ && eq@ <= end@
        && (forall<i: Int> 0 <= i && i < start@ ==> input@[i]@ == 38)
        && (forall<i: Int> start@ <= i && i < end@ ==> input@[i]@ != 38)
        && (forall<i: Int> start@ <= i && i < eq@ ==> input@[i]@ != 61)
        && (eq@ < end@ ==> input@[eq@]@ == 61)
        && (end@ < input@.len() ==> input@[end@]@ == 38)
        && raw_pair_model(input@, start@) == Some((start@, eq@, end@, next@))
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
        #[cfg(creusot)]
        proof_assert!(skip_ampersands_endpoint(input@, 0, start@));
        return None;
    }
    #[cfg(creusot)]
    proof_assert!(skip_ampersands_endpoint(input@, 0, start@));

    let mut end = start;
    #[cfg_attr(creusot, invariant(start@ <= end@ && end@ <= input@.len()
        && forall<i: Int> start@ <= i && i < end@ ==> input@[i]@ != 38))]
    while end < input.len() && input[end] != b'&' {
        end += 1;
    }
    #[cfg(creusot)]
    proof_assert!(find_byte_before_endpoint(input@, start@, end@, input@.len(), 38));

    let mut eq = start;
    #[cfg_attr(creusot, invariant(start@ <= eq@ && eq@ <= end@
        && forall<i: Int> start@ <= i && i < eq@ ==> input@[i]@ != 61))]
    while eq < end && input[eq] != b'=' {
        eq += 1;
    }
    #[cfg(creusot)]
    proof_assert!(find_byte_before_endpoint(input@, start@, eq@, end@, 61));

    let next = if end < input.len() { end + 1 } else { end };
    Some((start, eq, end, next))
}

#[cfg_attr(creusot, requires(start@ <= end@ && end@ <= input@.len()))]
#[cfg_attr(creusot, ensures(result@ == input@.subsequence(start@, end@)))]
fn slice_range(input: &[u8], start: usize, end: usize) -> &[u8] {
    let suffix = input.split_at(start).1;
    #[cfg(creusot)]
    proof_assert!(tail_prefix(input@, start@, end@));
    suffix.split_at(end - start).0
}

#[cfg_attr(creusot, requires(eq@ < end@ && end@ <= input@.len()))]
#[cfg_attr(creusot, ensures(result@ == input@.subsequence(eq@ + 1, end@)))]
fn slice_after_equals(input: &[u8], eq: usize, end: usize) -> &[u8] {
    slice_range(input, eq + 1, end)
}

#[cfg_attr(creusot, requires(index@ <= input@.len()))]
#[cfg_attr(creusot, ensures(result@ == Seq::<u8>::empty()))]
fn empty_slice_at(input: &[u8], index: usize) -> &[u8] {
    let empty = slice_range(input, index, index);
    #[cfg(creusot)]
    proof_assert!(input@.subsequence(index@, index@) == Seq::<u8>::empty());
    empty
}

#[cfg(creusot)]
impl IteratorSpec for Parse<'_> {
    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, other: Self) -> bool {
        pearlite! {
            parsed_trace(self.remaining_input())
                == visited.map(|(key, value)| (cow_str_scalars(key), cow_str_scalars(value)))
                    .concat(parsed_trace(other.remaining_input()))
            && parsed_borrow_trace(self.remaining_input())
                == visited.map(|(key, value)| (
                    ownership_model::cow_str_borrowed(key),
                    ownership_model::cow_str_borrowed(value),
                )).concat(parsed_borrow_trace(other.remaining_input()))
        }
    }

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            self.remaining_input().len() == skip_ampersands(self.remaining_input(), 0)
                && (^self).remaining_input() == Seq::empty()
        }
    }

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {
        proof_assert!(Seq::<(Cow<'_, str>, Cow<'_, str>)>::empty()
            .map(|(key, value)| (cow_str_scalars(key), cow_str_scalars(value)))
            .ext_eq(Seq::<(Seq<Int>, Seq<Int>)>::empty()));
        proof_assert!(Seq::<(Cow<'_, str>, Cow<'_, str>)>::empty()
            .map(|(key, value)| (
                ownership_model::cow_str_borrowed(key),
                ownership_model::cow_str_borrowed(value),
            )).ext_eq(Seq::<(bool, bool)>::empty()));
        proof_assert!({
            let trace = parsed_trace(self.remaining_input());
            let borrow_trace = parsed_borrow_trace(self.remaining_input());
            trace.concat_empty() == () && trace == Seq::empty().concat(trace)
                && borrow_trace.concat_empty() == ()
                && borrow_trace == Seq::empty().concat(borrow_trace)
        });
    }

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(
        a: Self,
        ab: Seq<Self::Item>,
        b: Self,
        bc: Seq<Self::Item>,
        c: Self,
    ) {
        proof_assert!({
            let ab_trace = ab.map(|(key, value)|
                (cow_str_scalars(key), cow_str_scalars(value)));
            let bc_trace = bc.map(|(key, value)|
                (cow_str_scalars(key), cow_str_scalars(value)));
            let tail = parsed_trace(c.remaining_input());
            let ab_borrow = ab.map(|(key, value)| (
                ownership_model::cow_str_borrowed(key),
                ownership_model::cow_str_borrowed(value),
            ));
            let bc_borrow = bc.map(|(key, value)| (
                ownership_model::cow_str_borrowed(key),
                ownership_model::cow_str_borrowed(value),
            ));
            let borrow_tail = parsed_borrow_trace(c.remaining_input());
            ab_trace.concat_assoc(bc_trace, tail) == ()
                && cow_pair_map_concat(ab, bc)
                && ab_borrow.concat_assoc(bc_borrow, borrow_tail) == ()
                && cow_pair_borrow_map_concat(ab, bc)
        });
    }
}

impl<'a> Iterator for Parse<'a> {
    type Item = (Cow<'a, str>, Cow<'a, str>);

    #[cfg_attr(creusot, ensures(match result {
        None => (^self).remaining_input() == Seq::empty()
            && self.remaining_input().len()
                == skip_ampersands(self.remaining_input(), 0),
        Some((key, value)) => (^self).remaining_input()
                == parse_suffix_after_next(self.remaining_input())
            && parsed_trace(self.remaining_input()) == Seq::singleton((
                cow_str_scalars(key), cow_str_scalars(value),
            )).concat(parsed_trace((^self).remaining_input()))
            && parsed_borrow_trace(self.remaining_input()) == Seq::singleton((
                ownership_model::cow_str_borrowed(key),
                ownership_model::cow_str_borrowed(value),
            )).concat(parsed_borrow_trace((^self).remaining_input()))
            && (*self).produces(Seq::singleton((key, value)), ^self),
    }))]
    fn next(&mut self) -> Option<Self::Item> {
        let input = self.input;
        match raw_pair_bounds(input) {
            None => {
                self.input = input.split_at(input.len()).1;
                None
            }
            Some((start, eq, end, next)) => {
                #[cfg(creusot)]
                proof_assert!(raw_pair_model(input@, start@)
                    == Some((start@, eq@, end@, next@)));
                #[cfg(creusot)]
                proof_assert!(parsed_trace_step(input@, start@, eq@, end@, next@));
                #[cfg(creusot)]
                proof_assert!(parsed_trace(input@) == Seq::singleton((
                    decoded_string_model(input@.subsequence(start@, eq@)),
                    decoded_string_model(if eq < end {
                        input@.subsequence(eq@ + 1, end@)
                    } else {
                        Seq::<u8>::empty()
                    }),
                )).concat(parsed_trace(input@.subsequence(next@, input@.len()))));
                #[cfg(creusot)]
                proof_assert!(parsed_borrow_trace_step(input@, start@, eq@, end@, next@));
                #[cfg(creusot)]
                proof_assert!(parsed_borrow_trace(input@) == Seq::singleton((
                    ownership_model::decode_borrows(input@.subsequence(start@, eq@)),
                    ownership_model::decode_borrows(if eq < end {
                        input@.subsequence(eq@ + 1, end@)
                    } else {
                        Seq::<u8>::empty()
                    }),
                )).concat(parsed_borrow_trace(input@.subsequence(next@, input@.len()))));
                #[cfg(creusot)]
                proof_assert!(tail_prefix(input@, start@, eq@));
                #[cfg(creusot)]
                proof_assert!(tail_prefix(input@, if eq < end { eq@ + 1 } else { eq@ }, end@));
                #[cfg(creusot)]
                proof_assert!(input@.subsequence(end@, end@) == Seq::<u8>::empty());
                let name = slice_range(input, start, eq);
                let value = if eq < end {
                    slice_after_equals(input, eq, end)
                } else {
                    empty_slice_at(input, end)
                };
                self.input = input.split_at(next).1;
                let pair = (decode(name), decode(value));
                #[cfg(creusot)]
                proof_assert!(self.remaining_input() == parse_suffix_after_next(input@));
                #[cfg(creusot)]
                proof_assert!(parsed_trace(input@) == Seq::singleton((
                    cow_str_scalars(pair.0), cow_str_scalars(pair.1),
                )).concat(parsed_trace(self.remaining_input())));
                #[cfg(creusot)]
                proof_assert!(parsed_borrow_trace(input@) == Seq::singleton((
                    ownership_model::cow_str_borrowed(pair.0),
                    ownership_model::cow_str_borrowed(pair.1),
                )).concat(parsed_borrow_trace(self.remaining_input())));
                #[cfg(creusot)]
                proof_assert!(cow_pair_singleton(pair.0, pair.1));
                #[cfg(creusot)]
                proof_assert!(cow_pair_borrow_singleton(pair.0, pair.1));
                Some(pair)
            }
        }
    }
}

#[cfg_attr(creusot, ensures(cow_str_scalars(result) == decoded_string_model(input@)))]
#[cfg_attr(creusot, ensures(ownership_model::cow_str_borrowed(result)
    == ownership_model::decode_borrows(input@)))]
fn decode(input: &[u8]) -> Cow<'_, str> {
    let replaced = replace_plus(input);
    let decoded = match &replaced {
        Cow::Borrowed(bytes) => percent_decode_local(bytes),
        Cow::Owned(bytes) => percent_decode_local(<Vec<u8> as core::ops::Deref>::deref(bytes)),
    };
    decode_utf8_lossy(match decoded {
        Cow::Owned(bytes) => Cow::Owned(bytes),
        Cow::Borrowed(_) => replaced,
    })
}

#[cfg(creusot)]
#[logic(open)]
pub fn string_scalars(s: Seq<char>) -> Seq<Int> {
    pearlite! { s.map(|c: char| c@) }
}

#[cfg(creusot)]
#[logic(open)]
pub fn cow_str_scalars(value: Cow<'_, str>) -> Seq<Int> {
    match value {
        Cow::Borrowed(s) => pearlite! { string_scalars(s@) },
        Cow::Owned(s) => pearlite! { string_scalars(s@) },
    }
}

#[cfg_attr(creusot, ensures(match result {
    Some(value) => percent_hex_value_model(byte@) == value@
        && 0 <= value@ && value@ <= 15,
    None => percent_hex_value_model(byte@) == -1,
}))]
fn percent_hex_value(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}

#[cfg(creusot)]
#[logic(open)]
pub fn percent_hex_value_model(byte: Int) -> Int {
    if 48 <= byte && byte <= 57 {
        byte - 48
    } else if 65 <= byte && byte <= 70 {
        byte - 55
    } else if 97 <= byte && byte <= 102 {
        byte - 87
    } else {
        -1
    }
}

#[cfg(creusot)]
#[logic(open)]
pub fn byte_sequence_as_ints(bytes: Seq<u8>) -> Seq<Int> {
    pearlite! { bytes.map(|byte: u8| byte@) }
}

#[cfg(creusot)]
#[logic(open)]
#[variant(bytes.len())]
pub fn percent_decoded_model(bytes: Seq<Int>) -> Seq<Int> {
    percent_decoded_from(bytes, 0)
}

#[cfg(creusot)]
#[logic]
#[requires(0 <= index && index <= bytes.len())]
#[variant(bytes.len() - index)]
pub fn percent_decoded_from(bytes: Seq<Int>, index: Int) -> Seq<Int> {
    if index == bytes.len() {
        Seq::empty()
    } else {
        let first = bytes[index];
        if first == 37 && index + 3 <= bytes.len() {
            let high = percent_hex_value_model(bytes[index + 1]);
            let low = percent_hex_value_model(bytes[index + 2]);
            if high >= 0 && low >= 0 {
                Seq::singleton(high * 16 + low)
                    .concat(percent_decoded_from(bytes, index + 3))
            } else {
                Seq::singleton(first)
                    .concat(percent_decoded_from(bytes, index + 1))
            }
        } else {
            Seq::singleton(first)
                .concat(percent_decoded_from(bytes, index + 1))
        }
    }
}

#[cfg(creusot)]
#[logic(opaque)]
#[requires(0 <= index && index < bytes.len())]
#[ensures(result)]
#[ensures(percent_decoded_from(bytes, index) == if bytes[index] == 37
    && index + 3 <= bytes.len()
    && percent_hex_value_model(bytes[index + 1]) >= 0
    && percent_hex_value_model(bytes[index + 2]) >= 0 {
        Seq::singleton(percent_hex_value_model(bytes[index + 1]) * 16
            + percent_hex_value_model(bytes[index + 2]))
            .concat(percent_decoded_from(bytes, index + 3))
    } else {
        Seq::singleton(bytes[index]).concat(percent_decoded_from(bytes, index + 1))
    })]
pub fn percent_decoded_from_step(bytes: Seq<Int>, index: Int) -> bool {
    true
}

#[cfg(creusot)]
#[logic(opaque)]
#[requires(0 <= start && start <= end && end <= bytes.len())]
#[ensures(result)]
#[ensures(byte_sequence_as_ints(bytes.subsequence(start, end))
    == byte_sequence_as_ints(bytes).subsequence(start, end))]
pub fn byte_model_subsequence(bytes: Seq<u8>, start: Int, end: Int) -> bool {
    true
}

#[cfg(creusot)]
#[logic(open)]
pub fn decoded_string_model(bytes: Seq<u8>) -> Seq<Int> {
    stdlib_models::utf8_lossy_model(percent_decoded_model(
        byte_sequence_as_ints(replace_plus_model(bytes)),
    ))
}

#[cfg(creusot)]
#[logic(open)]
#[requires(0 <= start && start <= input.len())]
#[variant(input.len() - start)]
#[ensures(start <= result && result <= input.len())]
#[ensures(forall<i: Int> start <= i && i < result ==> input[i]@ == 38)]
#[ensures(result == input.len() || input[result]@ != 38)]
pub fn skip_ampersands(input: Seq<u8>, start: Int) -> Int {
    if start < input.len() && pearlite! { input[start]@ } == 38 {
        skip_ampersands(input, start + 1)
    } else {
        start
    }
}

#[cfg(creusot)]
#[logic(open)]
#[requires(0 <= start && start <= end && end <= input.len())]
#[variant(end - start)]
#[ensures(start <= result && result <= end)]
#[ensures(forall<i: Int> start <= i && i < result ==> input[i]@ != byte)]
#[ensures(result == end || input[result]@ == byte)]
pub fn find_byte_before(input: Seq<u8>, start: Int, end: Int, byte: Int) -> Int {
    if start < end && pearlite! { input[start]@ } != byte {
        find_byte_before(input, start + 1, end, byte)
    } else {
        start
    }
}

#[cfg(creusot)]
#[logic]
#[requires(0 <= start && start <= end && end <= input.len())]
#[requires(forall<i: Int> start <= i && i < end ==> input[i]@ == 38)]
#[requires(end == input.len() || input[end]@ != 38)]
#[variant(end - start)]
#[ensures(result)]
#[ensures(skip_ampersands(input, start) == end)]
pub fn skip_ampersands_endpoint(input: Seq<u8>, start: Int, end: Int) -> bool {
    if start < end {
        skip_ampersands_endpoint(input, start + 1, end)
    } else {
        true
    }
}

#[cfg(creusot)]
#[logic]
#[requires(0 <= start && start <= end && end <= limit && limit <= input.len())]
#[requires(forall<i: Int> start <= i && i < end ==> input[i]@ != byte)]
#[requires(end == limit || input[end]@ == byte)]
#[variant(end - start)]
#[ensures(result)]
#[ensures(find_byte_before(input, start, limit, byte) == end)]
pub fn find_byte_before_endpoint(
    input: Seq<u8>,
    start: Int,
    end: Int,
    limit: Int,
    byte: Int,
) -> bool {
    if start < end {
        find_byte_before_endpoint(input, start + 1, end, limit, byte)
    } else {
        true
    }
}

#[cfg(creusot)]
#[logic(open)]
#[requires(start == skip_ampersands(input, 0))]
#[requires(start < input.len())]
#[ensures(match result {
    Some((pair_start, eq, end, next)) => pair_start == start
        && pair_start < end && end <= input.len()
        && pair_start <= eq && eq <= end
        && (eq < end ==> input[eq]@ == 61)
        && (end == input.len() || input[end]@ == 38)
        && next == if end < input.len() { end + 1 } else { end },
    None => false,
})]
pub fn raw_pair_model(input: Seq<u8>, start: Int) -> Option<(Int, Int, Int, Int)> {
    let end = find_byte_before(input, start, input.len(), 38);
    let eq = find_byte_before(input, start, end, 61);
    let next = if end < input.len() { end + 1 } else { end };
    Some((start, eq, end, next))
}

#[cfg(creusot)]
#[logic(open)]
#[variant(input.len())]
pub fn parsed_trace(input: Seq<u8>) -> Seq<(Seq<Int>, Seq<Int>)> {
    let start = skip_ampersands(input, 0);
    if start == input.len() {
        Seq::empty()
    } else {
        match raw_pair_model(input, start) {
            Some((pair_start, eq, end, next)) => {
                let name = input.subsequence(pair_start, eq);
                let value = if eq < end {
                    input.subsequence(eq + 1, end)
                } else {
                    Seq::empty()
                };
                Seq::singleton((decoded_string_model(name), decoded_string_model(value)))
                    .concat(parsed_trace(input.subsequence(next, input.len())))
            }
            None => Seq::empty(),
        }
    }
}

#[cfg(creusot)]
#[logic(open)]
#[variant(input.len())]
pub fn parsed_borrow_trace(input: Seq<u8>) -> Seq<(bool, bool)> {
    let start = skip_ampersands(input, 0);
    if start == input.len() {
        Seq::empty()
    } else {
        match raw_pair_model(input, start) {
            Some((pair_start, eq, end, next)) => {
                let name = input.subsequence(pair_start, eq);
                let value = if eq < end {
                    input.subsequence(eq + 1, end)
                } else {
                    Seq::empty()
                };
                Seq::singleton((
                    ownership_model::decode_borrows(name),
                    ownership_model::decode_borrows(value),
                )).concat(parsed_borrow_trace(input.subsequence(next, input.len())))
            }
            None => Seq::empty(),
        }
    }
}

#[cfg(creusot)]
#[logic(open)]
pub fn parse_suffix_after_next(input: Seq<u8>) -> Seq<u8> {
    let start = skip_ampersands(input, 0);
    if start == input.len() {
        Seq::empty()
    } else {
        match raw_pair_model(input, start) {
            Some((_, _, _, next)) => input.subsequence(next, input.len()),
            None => Seq::empty(),
        }
    }
}

#[cfg(creusot)]
#[logic(opaque)]
#[requires(0 <= start && start < end && end <= input.len())]
#[requires(start <= eq && eq <= end)]
#[requires(0 <= next && next <= input.len())]
#[requires(start == skip_ampersands(input, 0))]
#[requires(raw_pair_model(input, start) == Some((start, eq, end, next)))]
#[ensures(result)]
#[ensures(parse_suffix_after_next(input) == input.subsequence(next, input.len()))]
#[ensures(parsed_trace(input) == Seq::singleton((
    decoded_string_model(input.subsequence(start, eq)),
    decoded_string_model(if eq < end {
        input.subsequence(eq + 1, end)
    } else {
        Seq::empty()
    }),
)).concat(parsed_trace(input.subsequence(next, input.len()))))]
pub fn parsed_trace_step(
    input: Seq<u8>,
    start: Int,
    eq: Int,
    end: Int,
    next: Int,
) -> bool {
    true
}

#[cfg(creusot)]
#[logic(opaque)]
#[requires(0 <= start && start < end && end <= input.len())]
#[requires(start <= eq && eq <= end)]
#[requires(0 <= next && next <= input.len())]
#[requires(start == skip_ampersands(input, 0))]
#[requires(raw_pair_model(input, start) == Some((start, eq, end, next)))]
#[ensures(result)]
#[ensures(parsed_borrow_trace(input) == Seq::singleton((
    ownership_model::decode_borrows(input.subsequence(start, eq)),
    ownership_model::decode_borrows(if eq < end {
        input.subsequence(eq + 1, end)
    } else {
        Seq::empty()
    }),
)).concat(parsed_borrow_trace(input.subsequence(next, input.len()))))]
pub fn parsed_borrow_trace_step(
    input: Seq<u8>,
    start: Int,
    eq: Int,
    end: Int,
    next: Int,
) -> bool {
    true
}

/// Decode valid `%HH` escapes and leave malformed or incomplete escapes intact.
#[cfg_attr(creusot, ensures(match result {
    Cow::Borrowed(bytes) => percent_decoded_model(byte_sequence_as_ints(input@))
        == byte_sequence_as_ints(bytes@)
        && bytes@ == input@ && percent_decoded_model(byte_sequence_as_ints(input@)).len() == input@.len(),
    Cow::Owned(bytes) => percent_decoded_model(byte_sequence_as_ints(input@))
        == byte_sequence_as_ints(bytes@)
        && percent_decoded_model(byte_sequence_as_ints(input@)).len() < input@.len(),
}))]
fn percent_decode_local(input: &[u8]) -> Cow<'_, [u8]> {
    #[cfg(creusot)]
    let _ = Seq::<Int>::concat_empty;
    #[cfg(creusot)]
    let _ = Seq::<Int>::concat_assoc;
    let mut output: Option<Vec<u8>> = None;
    let mut index = 0;
    #[cfg_attr(creusot, invariant(0 <= index@ && index@ <= input@.len()
        && percent_decoded_model(byte_sequence_as_ints(input@)) ==
            (match output {
                Some(bytes) => byte_sequence_as_ints(bytes@),
                None => byte_sequence_as_ints(input@).subsequence(0, index@),
            }).concat(percent_decoded_from(byte_sequence_as_ints(input@), index@))))]
    #[cfg_attr(creusot, invariant(match output {
            Some(bytes) => bytes@.len() < index@,
            None => true,
        }))]
    while index < input.len() {
        let decoded = if input[index] == b'%' && input.len() - index >= 3 {
            match (percent_hex_value(input[index + 1]), percent_hex_value(input[index + 2])) {
                (Some(high), Some(low)) => Some(high * 16 + low),
                _ => None,
            }
        } else {
            None
        };
        match decoded {
            Some(byte) => {
                #[cfg(creusot)]
                let old_prefix = creusot_std::prelude::snapshot!(pearlite! { match output {
                    Some(bytes) => byte_sequence_as_ints(bytes@),
                    None => byte_sequence_as_ints(input@).subsequence(0, index@),
                }});
                #[cfg(creusot)]
                proof_assert!(percent_decoded_from_step(
                    byte_sequence_as_ints(input@), index@
                ));
                #[cfg(creusot)]
                proof_assert!(percent_decoded_from(
                    byte_sequence_as_ints(input@), index@
                ) == Seq::singleton(byte@).concat(percent_decoded_from(
                    byte_sequence_as_ints(input@), index@ + 3
                )));
                #[cfg(creusot)]
                proof_assert!(byte_model_subsequence(input@, 0, index@));
                #[cfg(creusot)]
                proof_assert!({
                    let prefix = pearlite! { match output {
                        Some(bytes) => byte_sequence_as_ints(bytes@),
                        None => byte_sequence_as_ints(input@).subsequence(0, index@),
                    }};
                    let one = Seq::singleton(byte@);
                    let rest = percent_decoded_from(byte_sequence_as_ints(input@), index@ + 3);
                    prefix.concat_assoc(one, rest) == ()
                        && prefix.concat(one).concat(rest) == prefix.concat(one.concat(rest))
                });
                append_decoded_byte(&mut output, input, index, byte);
                #[cfg(creusot)]
                proof_assert!(match output {
                    Some(bytes) => byte_sequence_as_ints(bytes@)
                        == (*old_prefix).concat(Seq::singleton(byte@)),
                    None => false,
                });
                index += 3;
            }
            None => {
                #[cfg(creusot)]
                let old_prefix = creusot_std::prelude::snapshot!(pearlite! { match output {
                    Some(bytes) => byte_sequence_as_ints(bytes@),
                    None => byte_sequence_as_ints(input@).subsequence(0, index@),
                }});
                #[cfg(creusot)]
                proof_assert!(percent_decoded_from_step(
                    byte_sequence_as_ints(input@), index@
                ));
                #[cfg(creusot)]
                proof_assert!(percent_decoded_from(
                    byte_sequence_as_ints(input@), index@
                ) == Seq::singleton(input[index]@).concat(percent_decoded_from(
                    byte_sequence_as_ints(input@), index@ + 1
                )));
                #[cfg(creusot)]
                proof_assert!(byte_int_prefix_push(input@, index@));
                #[cfg(creusot)]
                proof_assert!({
                    let one = Seq::singleton(input[index]@);
                    let rest = percent_decoded_from(byte_sequence_as_ints(input@), index@ + 1);
                    (*old_prefix).concat_assoc(one, rest) == ()
                        && (*old_prefix).concat(one).concat(rest)
                            == (*old_prefix).concat(one.concat(rest))
                });
                append_literal_byte(&mut output, input, index);
                #[cfg(creusot)]
                proof_assert!(match output {
                    Some(bytes) => byte_sequence_as_ints(bytes@)
                        == (*old_prefix).concat(Seq::singleton(input[index]@)),
                    None => byte_sequence_as_ints(input@).subsequence(0, index@ + 1)
                        == (*old_prefix).concat(Seq::singleton(input[index]@)),
                });
                index += 1;
            }
        }
    }
    match output {
        Some(bytes) => Cow::Owned(bytes),
        None => Cow::Borrowed(input),
    }
}

#[cfg_attr(creusot, ensures((^bytes)@ == bytes@.push_back(byte)))]
#[cfg_attr(creusot, ensures(byte_sequence_as_ints((^bytes)@)
    == byte_sequence_as_ints(bytes@).concat(Seq::singleton(byte@))))]
#[cfg_attr(creusot, ensures((^bytes)@.len() == bytes@.len() + 1))]
fn push_byte_preserving_map(bytes: &mut Vec<u8>, byte: u8) {
    bytes.push(byte);
}

#[cfg_attr(creusot, ensures(result@.ext_eq(input@)))]
fn copy_bytes(input: &[u8]) -> Vec<u8> {
    let copied = input.to_vec();
    #[cfg(creusot)]
    proof_assert!(copied@.ext_eq(input@));
    copied
}

#[cfg_attr(creusot, requires(index@ + 3 <= input@.len()))]
#[cfg_attr(creusot, requires(match *output {
    Some(before) => before@.len() < index@,
    None => true,
}))]
#[cfg_attr(creusot, ensures(match ^output {
    Some(after) => after@ == (match *output {
        Some(before) => before@,
        None => input@.subsequence(0, index@),
    }).push_back(byte),
    None => false,
}))]
#[cfg_attr(creusot, ensures(match ^output {
    Some(after) => byte_sequence_as_ints(after@)
        == (match *output {
        Some(before) => byte_sequence_as_ints(before@),
        None => byte_sequence_as_ints(input@).subsequence(0, index@),
        }).concat(Seq::singleton(byte@)),
    None => false,
}))]
#[cfg_attr(creusot, ensures(match ^output {
    Some(after) => after@.len() == match *output {
        Some(before) => before@.len() + 1,
        None => index@ + 1,
    },
    None => false,
}))]
#[cfg_attr(creusot, ensures(match ^output {
    Some(after) => after@.len() < index@ + 3,
    None => false,
}))]
fn append_decoded_byte(output: &mut Option<Vec<u8>>, input: &[u8], index: usize, byte: u8) {
    if output.is_none() {
        let prefix = input.split_at(index).0;
        *output = Some(copy_bytes(prefix));
    }
    if let Some(bytes) = output {
        push_byte_preserving_map(bytes, byte);
    }
}

#[cfg_attr(creusot, requires(index@ < input@.len()))]
#[cfg_attr(creusot, requires(match *output {
    Some(before) => before@.len() < index@,
    None => true,
}))]
#[cfg_attr(creusot, ensures(match (*output, ^output) {
    (None, None) => true,
    (Some(before), Some(after)) => after@ == before@.push_back(input[index])
        && byte_sequence_as_ints(after@)
            == byte_sequence_as_ints(before@)
                .concat(Seq::singleton(input[index]@)),
    _ => false,
}))]
#[cfg_attr(creusot, ensures(match ^output {
    None => byte_sequence_as_ints(input@).subsequence(0, index@ + 1)
        == byte_sequence_as_ints(input@).subsequence(0, index@)
            .concat(Seq::singleton(input[index]@)),
    Some(after) => after@.len() < index@ + 1,
}))]
#[cfg_attr(creusot, ensures(match (*output, ^output) {
    (None, None) => true,
    (Some(before), Some(after)) => after@.len() == before@.len() + 1,
    _ => false,
}))]
fn append_literal_byte(output: &mut Option<Vec<u8>>, input: &[u8], index: usize) {
    #[cfg(creusot)]
    proof_assert!(byte_int_prefix_push(input@, index@));
    if let Some(bytes) = output {
        push_byte_preserving_map(bytes, input[index]);
    }
}

#[cfg(creusot)]
#[logic(opaque)]
#[requires(0 <= index && index < bytes.len())]
#[ensures(result)]
#[ensures(bytes.subsequence(0, index + 1)
    == bytes.subsequence(0, index).concat(Seq::singleton(bytes[index])))]
pub fn int_prefix_push(bytes: Seq<Int>, index: Int) -> bool {
    true
}

#[cfg(creusot)]
#[logic]
#[requires(bytes.len() == 3)]
#[requires(bytes[0]@ < 128 && bytes[1]@ < 128 && bytes[2]@ < 128)]
#[ensures(result)]
#[ensures(forall<i: Int> 0 <= i && i < bytes.len() ==> bytes[i]@ < 128)]
pub fn ascii_three(bytes: Seq<u8>) -> bool {
    pearlite! { forall<i: Int> 0 <= i && i < bytes.len() ==> bytes[i]@ < 128 }
}

#[cfg(creusot)]
#[logic]
#[requires(byte != 32 && bytes.len() == 3)]
#[requires(bytes[0]@ == 37)]
#[requires(bytes[1]@ == uppercase_hex(byte / 16))]
#[requires(bytes[2]@ == uppercase_hex(byte % 16))]
#[ensures(result)]
#[ensures(byte_sequence_as_ints(bytes) == escaped_byte_chunk(byte))]
pub fn encoded_array_model(bytes: Seq<u8>, byte: Int) -> bool {
    byte_sequence_as_ints(bytes).ext_eq(escaped_byte_chunk(byte))
}

#[cfg(creusot)]
#[logic]
#[requires(0 <= index && index < bytes.len())]
#[ensures(result)]
#[ensures(byte_sequence_as_ints(bytes).subsequence(0, index + 1)
    == byte_sequence_as_ints(bytes).subsequence(0, index)
        .concat(Seq::singleton(bytes[index]@)))]
pub fn byte_int_prefix_push(bytes: Seq<u8>, index: Int) -> bool {
    int_prefix_push(byte_sequence_as_ints(bytes), index)
        && pearlite! { byte_sequence_as_ints(bytes)[index] == bytes[index]@ }
}

#[cfg(creusot)]
#[logic]
#[requires(0 <= start && start <= end && end <= bytes.len())]
#[ensures(result)]
#[ensures(bytes.subsequence(start, bytes.len()).subsequence(0, end - start)
    == bytes.subsequence(start, end))]
pub fn tail_prefix(bytes: Seq<u8>, start: Int, end: Int) -> bool {
    bytes.subsequence(start, bytes.len()).subsequence(0, end - start)
        == bytes.subsequence(start, end)
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
#[cfg_attr(creusot, ensures(match result {
    Cow::Borrowed(bytes) => bytes@ == input@ && replace_plus_model(input@) == input@,
    Cow::Owned(bytes) => bytes@ == replace_plus_model(input@),
}))]
#[cfg_attr(creusot, ensures(ownership_model::cow_bytes_borrowed(result)
    == ownership_model::no_plus(input@)))]
fn replace_plus(input: &[u8]) -> Cow<'_, [u8]> {
    match find_plus(input) {
        None => {
            #[cfg(creusot)]
            proof_assert!(no_plus_identity(input@));
            Cow::Borrowed(input)
        }
        Some(first_position) => {
            let mut replaced = copy_bytes(input);
            replace_plus_in_place(&mut replaced, first_position);
            #[cfg(creusot)]
            proof_assert!(plus_result_exact(input@, replaced@));
            Cow::Owned(replaced)
        }
    }
}

impl<'a> Parse<'a> {
    /// Return a new iterator that yields pairs of `String` instead of pairs of `Cow<str>`.
    #[cfg_attr(creusot, ensures(result.remaining_owned_input() == self.remaining_input()))]
    pub fn into_owned(self) -> ParseIntoOwned<'a> {
        ParseIntoOwned { inner: self }
    }
}

/// Like `Parse`, but yields pairs of `String` instead of pairs of `Cow<str>`.
pub struct ParseIntoOwned<'a> {
    inner: Parse<'a>,
}

impl ParseIntoOwned<'_> {
    #[cfg(creusot)]
    #[logic(open(self), inline)]
    pub fn remaining_owned_input(self) -> Seq<u8> {
        pearlite! { self.inner.remaining_input() }
    }
}

#[cfg(creusot)]
impl IteratorSpec for ParseIntoOwned<'_> {
    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, other: Self) -> bool {
        pearlite! {
            parsed_trace(self.remaining_owned_input())
                == visited.map(|(key, value): (String, String)|
                    (string_scalars(key@), string_scalars(value@)))
                    .concat(parsed_trace(other.remaining_owned_input()))
        }
    }

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            self.remaining_owned_input().len()
                == skip_ampersands(self.remaining_owned_input(), 0)
                && (^self).remaining_owned_input() == Seq::empty()
        }
    }

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {
        proof_assert!(Seq::<(String, String)>::empty()
            .map(|(key, value): (String, String)|
                (string_scalars(key@), string_scalars(value@)))
            .ext_eq(Seq::<(Seq<Int>, Seq<Int>)>::empty()));
        proof_assert!({
            let trace = parsed_trace(self.remaining_owned_input());
            trace.concat_empty() == () && trace == Seq::empty().concat(trace)
        });
    }

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(
        a: Self,
        ab: Seq<Self::Item>,
        b: Self,
        bc: Seq<Self::Item>,
        c: Self,
    ) {
        proof_assert!({
            let ab_trace = ab.map(|(key, value): (String, String)|
                (string_scalars(key@), string_scalars(value@)));
            let bc_trace = bc.map(|(key, value): (String, String)|
                (string_scalars(key@), string_scalars(value@)));
            let tail = parsed_trace(c.remaining_owned_input());
            ab_trace.concat_assoc(bc_trace, tail) == ()
                && owned_pair_map_concat(ab, bc)
        });
    }
}

impl Iterator for ParseIntoOwned<'_> {
    type Item = (String, String);

    #[cfg_attr(creusot, ensures(match result {
        None => (^self).remaining_owned_input() == Seq::empty()
            && self.remaining_owned_input().len()
                == skip_ampersands(self.remaining_owned_input(), 0),
        Some((key, value)) => (^self).remaining_owned_input()
                == parse_suffix_after_next(self.remaining_owned_input())
            && parsed_trace(self.remaining_owned_input()) == Seq::singleton((
                string_scalars(key@), string_scalars(value@),
            )).concat(parsed_trace((^self).remaining_owned_input()))
            && (*self).produces(Seq::singleton((key, value)), ^self),
    }))]
    fn next(&mut self) -> Option<Self::Item> {
        let input = self.inner.input;
        match raw_pair_bounds(input) {
            None => {
                self.inner.input = input.split_at(input.len()).1;
                None
            }
            Some((start, eq, end, next)) => {
                #[cfg(creusot)]
                proof_assert!(raw_pair_model(input@, start@)
                    == Some((start@, eq@, end@, next@)));
                #[cfg(creusot)]
                proof_assert!(parsed_trace_step(input@, start@, eq@, end@, next@));
                #[cfg(creusot)]
                proof_assert!(parsed_trace(input@) == Seq::singleton((
                    decoded_string_model(input@.subsequence(start@, eq@)),
                    decoded_string_model(if eq < end {
                        input@.subsequence(eq@ + 1, end@)
                    } else {
                        Seq::<u8>::empty()
                    }),
                )).concat(parsed_trace(input@.subsequence(next@, input@.len()))));
                #[cfg(creusot)]
                proof_assert!(tail_prefix(input@, start@, eq@));
                #[cfg(creusot)]
                proof_assert!(tail_prefix(input@, if eq < end { eq@ + 1 } else { eq@ }, end@));
                #[cfg(creusot)]
                proof_assert!(input@.subsequence(end@, end@) == Seq::<u8>::empty());
                let name = slice_range(input, start, eq);
                let value = if eq < end {
                    slice_after_equals(input, eq, end)
                } else {
                    empty_slice_at(input, end)
                };
                self.inner.input = input.split_at(next).1;
                let pair = (cow_str_into_owned(decode(name)), cow_str_into_owned(decode(value)));
                #[cfg(creusot)]
                proof_assert!(owned_pair_singleton(pair.0, pair.1));
                Some(pair)
            }
        }
    }
}

#[cfg_attr(creusot, ensures(match value {
    Cow::Borrowed(s) => result@ == s@,
    Cow::Owned(s) => result@ == s@,
}))]
fn cow_str_into_owned(value: Cow<'_, str>) -> String {
    match value {
        Cow::Borrowed(s) => s.to_owned(),
        Cow::Owned(s) => s,
    }
}

/// The [`application/x-www-form-urlencoded` byte serializer](
/// https://url.spec.whatwg.org/#concept-urlencoded-byte-serializer).
///
/// Return an iterator of `&str` slices.
#[cfg_attr(creusot, ensures(result.remaining_bytes() == input@))]
pub fn byte_serialize(input: &[u8]) -> ByteSerialize<'_> {
    ByteSerialize { bytes: input }
}

/// Return value of `byte_serialize()`.
#[derive(Debug)]
pub struct ByteSerialize<'a> {
    bytes: &'a [u8],
}

impl ByteSerialize<'_> {
    #[cfg(creusot)]
    #[logic(open(self), inline)]
    pub fn remaining_bytes(self) -> Seq<u8> {
        pearlite! { self.bytes@ }
    }
}

#[cfg_attr(creusot, ensures(result.0@ == if bytes@.len() == 0 { 0 } else { 1 }
    && match result.1 {
        Some(n) => n@ == if bytes@.len() == 0 { 0 } else { bytes@.len() },
        None => false,
    }))]
fn byte_serialize_size_hint(bytes: &[u8]) -> (usize, Option<usize>) {
    if bytes.len() == 0 {
        (0, Some(0))
    } else {
        (1, Some(bytes.len()))
    }
}

#[cfg_attr(creusot, ensures(result == (byte@ == 42 || byte@ == 45 || byte@ == 46
    || 48 <= byte@ && byte@ <= 57 || 65 <= byte@ && byte@ <= 90 || byte@ == 95
    || 97 <= byte@ && byte@ <= 122)))]
fn byte_serialized_unchanged(byte: u8) -> bool {
    matches!(byte, b'*' | b'-' | b'.' | b'0' ..= b'9' | b'A' ..= b'Z' | b'_' | b'a' ..= b'z')
}

#[cfg(creusot)]
#[logic(open)]
#[ensures(result == (byte == 42 || byte == 45 || byte == 46
    || 48 <= byte && byte <= 57 || 65 <= byte && byte <= 90 || byte == 95
    || 97 <= byte && byte <= 122))]
pub fn unchanged_byte(byte: Int) -> bool {
    byte == 42 || byte == 45 || byte == 46
        || 48 <= byte && byte <= 57 || 65 <= byte && byte <= 90 || byte == 95
        || 97 <= byte && byte <= 122
}

#[cfg(creusot)]
#[logic(open)]
#[ensures(result == if digit < 10 { 48 + digit } else { 55 + digit })]
pub fn uppercase_hex(digit: Int) -> Int {
    if digit < 10 { 48 + digit } else { 55 + digit }
}

#[cfg(creusot)]
#[logic(open)]
#[requires(0 <= start && start <= bytes.len())]
#[variant(bytes.len() - start)]
#[ensures(start <= result && result <= bytes.len())]
#[ensures(forall<i: Int> start <= i && i < result ==> unchanged_byte(bytes[i]@))]
#[ensures(result == bytes.len() || !unchanged_byte(bytes[result]@))]
#[ensures(start < bytes.len() && unchanged_byte(bytes[start]@) ==> start < result)]
pub fn safe_run_end(bytes: Seq<u8>, start: Int) -> Int {
    if start < bytes.len() && unchanged_byte(pearlite! { bytes[start]@ }) {
        safe_run_end(bytes, start + 1)
    } else {
        start
    }
}

#[cfg(creusot)]
#[logic(open)]
pub fn escaped_byte_chunk(byte: Int) -> Seq<Int> {
    if byte == 32 {
        Seq::singleton(43)
    } else {
        Seq::singleton(37)
            .concat(Seq::singleton(uppercase_hex(byte / 16)))
            .concat(Seq::singleton(uppercase_hex(byte % 16)))
    }
}

#[cfg(creusot)]
#[logic(open)]
#[variant(bytes.len())]
#[ensures((bytes.len() == 0) == (result.len() == 0))]
#[ensures(bytes.len() > 0 ==> 1 <= result.len() && result.len() <= bytes.len())]
pub fn encoded_chunks(bytes: Seq<u8>) -> Seq<Seq<Int>> {
    if bytes.len() == 0 {
        Seq::empty()
    } else {
        let byte = pearlite! { bytes[0]@ };
        if unchanged_byte(byte) {
            let end = safe_run_end(bytes, 0);
            pearlite! { Seq::singleton(bytes.subsequence(0, end).map(|b: u8| b@))
                .concat(encoded_chunks(bytes.subsequence(end, bytes.len()))) }
        } else {
            Seq::singleton(escaped_byte_chunk(byte))
                .concat(encoded_chunks(bytes.subsequence(1, bytes.len())))
        }
    }
}

#[cfg(creusot)]
#[logic(opaque)]
#[requires(bytes.len() > 0 && unchanged_byte(bytes[0]@)
    && end == safe_run_end(bytes, 0))]
#[ensures(result)]
#[ensures(encoded_chunks(bytes) == Seq::singleton(
    byte_sequence_as_ints(bytes.subsequence(0, end)))
        .concat(encoded_chunks(bytes.subsequence(end, bytes.len()))))]
pub fn encoded_chunks_first_run(bytes: Seq<u8>, end: Int) -> bool {
    true
}

#[cfg(creusot)]
#[logic(opaque)]
#[requires(bytes.len() > 0 && !unchanged_byte(bytes[0]@)
    && byte == bytes[0]@)]
#[ensures(result)]
#[ensures(encoded_chunks(bytes) == Seq::singleton(escaped_byte_chunk(byte))
    .concat(encoded_chunks(bytes.subsequence(1, bytes.len()))))]
pub fn encoded_chunks_first_escaped(bytes: Seq<u8>, byte: Int) -> bool {
    true
}

#[cfg(creusot)]
#[logic(open)]
pub fn string_chunk_bytes(s: &str) -> Seq<Int> {
    pearlite! { s@.to_bytes().map(|b: u8| b@) }
}

#[cfg(creusot)]
#[logic(opaque)]
#[ensures(result)]
#[ensures(Seq::singleton(s).map(|x: &str| string_chunk_bytes(x))
    == Seq::singleton(string_chunk_bytes(s)))]
pub fn string_chunk_singleton(s: &str) -> bool {
    true
}

#[cfg(creusot)]
#[logic(opaque)]
#[ensures(result)]
#[ensures(ab.concat(bc).map(|s: &str| string_chunk_bytes(s))
    == ab.map(|s: &str| string_chunk_bytes(s))
        .concat(bc.map(|s: &str| string_chunk_bytes(s))))]
pub fn string_chunk_map_concat(ab: Seq<&str>, bc: Seq<&str>) -> bool {
    true
}

#[cfg(creusot)]
#[logic(opaque)]
#[ensures(result)]
#[ensures(ab.concat(bc).map(|(key, value)|
        (cow_str_scalars(key), cow_str_scalars(value)))
    == ab.map(|(key, value)| (cow_str_scalars(key), cow_str_scalars(value)))
        .concat(bc.map(|(key, value)| (cow_str_scalars(key), cow_str_scalars(value)))))]
pub fn cow_pair_map_concat<'a>(
    ab: Seq<(Cow<'a, str>, Cow<'a, str>)>,
    bc: Seq<(Cow<'a, str>, Cow<'a, str>)>,
) -> bool {
    true
}

#[cfg(creusot)]
#[logic(opaque)]
#[ensures(result)]
#[ensures(ab.concat(bc).map(|(key, value): (String, String)|
        (string_scalars(key@), string_scalars(value@)))
    == ab.map(|(key, value): (String, String)|
        (string_scalars(key@), string_scalars(value@)))
        .concat(bc.map(|(key, value): (String, String)|
            (string_scalars(key@), string_scalars(value@)))))]
pub fn owned_pair_map_concat(
    ab: Seq<(String, String)>,
    bc: Seq<(String, String)>,
) -> bool {
    true
}

#[cfg(creusot)]
#[logic(opaque)]
#[ensures(result)]
#[ensures(Seq::singleton((key, value)).map(|(key, value)|
        (cow_str_scalars(key), cow_str_scalars(value)))
    == Seq::singleton((cow_str_scalars(key), cow_str_scalars(value))))]
pub fn cow_pair_singleton<'a>(key: Cow<'a, str>, value: Cow<'a, str>) -> bool {
    true
}

#[cfg(creusot)]
#[logic(opaque)]
#[ensures(result)]
#[ensures(Seq::singleton((key, value)).map(|(key, value)| (
    ownership_model::cow_str_borrowed(key),
    ownership_model::cow_str_borrowed(value),
)) == Seq::singleton((
    ownership_model::cow_str_borrowed(key),
    ownership_model::cow_str_borrowed(value),
)))]
pub fn cow_pair_borrow_singleton<'a>(key: Cow<'a, str>, value: Cow<'a, str>) -> bool {
    true
}

#[cfg(creusot)]
#[logic(opaque)]
#[ensures(result)]
#[ensures(ab.concat(bc).map(|(key, value)| (
    ownership_model::cow_str_borrowed(key),
    ownership_model::cow_str_borrowed(value),
)) == ab.map(|(key, value)| (
    ownership_model::cow_str_borrowed(key),
    ownership_model::cow_str_borrowed(value),
)).concat(bc.map(|(key, value)| (
    ownership_model::cow_str_borrowed(key),
    ownership_model::cow_str_borrowed(value),
))))]
pub fn cow_pair_borrow_map_concat<'a>(
    ab: Seq<(Cow<'a, str>, Cow<'a, str>)>,
    bc: Seq<(Cow<'a, str>, Cow<'a, str>)>,
) -> bool {
    true
}

#[cfg(creusot)]
#[logic(opaque)]
#[ensures(result)]
#[ensures(Seq::singleton((key, value)).map(|(key, value): (String, String)|
        (string_scalars(key@), string_scalars(value@)))
    == Seq::singleton((string_scalars(key@), string_scalars(value@))))]
pub fn owned_pair_singleton(key: String, value: String) -> bool {
    true
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

impl<'a> Iterator for ByteSerialize<'a> {
    type Item = &'a str;

    #[cfg_attr(creusot, ensures(match result {
        None => self.completed(),
        Some(v) => (*self).produces(Seq::singleton(v), ^self),
    }))]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((&first, tail)) = self.bytes.split_first() {
            if !byte_serialized_unchanged(first) {
                #[cfg(creusot)]
                proof_assert!(encoded_chunks_first_escaped(self.bytes@, first@));
                self.bytes = tail;
                let value = if first == b' ' {
                    // Use the same promoted static byte data as `"+"`, while
                    // keeping the proof at the numeric ASCII boundary.
                    let plus_bytes: &'static [u8; 1] = &[43u8];
                    #[cfg(creusot)]
                    proof_assert!(forall<i: Int> 0 <= i && i < plus_bytes@.len()
                        ==> plus_bytes@[i]@ < 128);
                    let plus = unsafe { str::from_utf8_unchecked(plus_bytes) };
                    #[cfg(creusot)]
                    proof_assert!(escaped_byte_chunk(first@) == Seq::singleton(43));
                    plus
                } else {
                    let encoded = percent_encoded_bytes(first);
                    #[cfg(creusot)]
                    proof_assert!(ascii_three(encoded@));
                    #[cfg(creusot)]
                    proof_assert!(encoded_array_model(encoded@, first@));
                    unsafe { str::from_utf8_unchecked(encoded) }
                };
                #[cfg(creusot)]
                proof_assert!(string_chunk_bytes(value) == escaped_byte_chunk(first@));
                #[cfg(creusot)]
                proof_assert!(string_chunk_singleton(value));
                return Some(value);
            }
            let mut run_len = 1;
            #[cfg_attr(creusot, invariant(1 <= run_len@ && run_len@ <= self.bytes@.len()
                && forall<i: Int> 0 <= i && i < run_len@ ==>
                    unchanged_byte(self.bytes@[i]@)))]
            while run_len < self.bytes.len()
                && byte_serialized_unchanged(self.bytes[run_len])
            {
                run_len += 1;
            }
            #[cfg(creusot)]
            proof_assert!(run_len@ == safe_run_end(self.bytes@, 0));
            #[cfg(creusot)]
            proof_assert!(encoded_chunks_first_run(self.bytes@, run_len@));
            let (unchanged_slice, remaining) = self.bytes.split_at(run_len);
            self.bytes = remaining;
            let value = unsafe { str::from_utf8_unchecked(unchanged_slice) };
            #[cfg(creusot)]
            proof_assert!(string_chunk_bytes(value) == byte_sequence_as_ints(unchanged_slice@));
            #[cfg(creusot)]
            proof_assert!(string_chunk_singleton(value));
            Some(value)
        } else {
            None
        }
    }

    #[cfg_attr(creusot, ensures(result.0@ == if self.remaining_bytes().len() == 0 { 0 }
        else { 1 }
        && match result.1 {
            Some(n) => n@ == if self.remaining_bytes().len() == 0 { 0 }
                else { self.remaining_bytes().len() },
            None => false,
        }))]
    fn size_hint(&self) -> (usize, Option<usize>) {
        byte_serialize_size_hint(self.bytes)
    }
}

#[cfg(creusot)]
impl IteratorSpec for ByteSerialize<'_> {
    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            encoded_chunks(self.remaining_bytes())
                == visited.map(|s: &str| string_chunk_bytes(s))
                    .concat(encoded_chunks(o.remaining_bytes()))
        }
    }

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.remaining_bytes().len() == 0 && resolve(self) }
    }

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {
        proof_assert!(Seq::<&str>::empty()
            .map(|s| string_chunk_bytes(s))
            .ext_eq(Seq::<Seq<Int>>::empty()));
        proof_assert!({
            let trace = encoded_chunks(self.remaining_bytes());
            trace.concat_empty() == () && trace == Seq::empty().concat(trace)
        });
    }

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {
        proof_assert!({
            let ab_bytes = ab.map(|s| string_chunk_bytes(s));
            let bc_bytes = bc.map(|s| string_chunk_bytes(s));
            let tail = encoded_chunks(c.remaining_bytes());
            ab_bytes.concat_assoc(bc_bytes, tail) == ()
                && string_chunk_map_concat(ab, bc)
        });
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

pub trait Target {
    fn as_mut_string(&mut self) -> &mut String;
    fn finish(self) -> Self::Finished;
    type Finished;
}

impl Target for String {
    #[cfg_attr(creusot, ensures(*result == *self && ^result == ^self))]
    fn as_mut_string(&mut self) -> &mut String {
        self
    }

    #[cfg_attr(creusot, ensures(result == self))]
    fn finish(self) -> Self {
        self
    }
    type Finished = Self;
}

impl Target for &mut String {
    #[cfg_attr(creusot, ensures(*result == **self
        && ^result == *^self
        && ^*self == ^^self))]
    fn as_mut_string(&mut self) -> &mut String {
        self
    }

    #[cfg_attr(creusot, ensures(result == self))]
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
#[cfg_attr(creusot, ensures(match input {
    Cow::Borrowed(bytes) => match result {
        Cow::Borrowed(s) => stdlib_models::utf8_is_valid(byte_sequence_as_ints(bytes@))
            && pearlite! { s@.map(|c: char| c@) }
                == stdlib_models::utf8_lossy_model(byte_sequence_as_ints(bytes@))
            && s@.to_bytes() == bytes@,
        Cow::Owned(s) => !stdlib_models::utf8_is_valid(byte_sequence_as_ints(bytes@))
            && pearlite! { s@.map(|c: char| c@) }
                == stdlib_models::utf8_lossy_model(byte_sequence_as_ints(bytes@)),
    },
    Cow::Owned(bytes) => match result {
        Cow::Borrowed(_) => false,
        Cow::Owned(s) => pearlite! { s@.map(|c: char| c@) }
            == stdlib_models::utf8_lossy_model(byte_sequence_as_ints(bytes@)),
    },
}))]
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
                    debug_assert_eq!(utf8.as_bytes(), &*bytes);

                    #[cfg(creusot)]
                    proof_assert!({
                        creusot_std::std::string::injective_to_bytes();
                        true
                    });

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
