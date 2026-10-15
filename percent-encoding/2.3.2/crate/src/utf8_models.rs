//! UTF-8 models and the `Cow` decoding helpers.
//!
//! Strict validity and successful string content are modeled at the standard
//! library boundary. Error detail fields are tied to a local UTF-8 recognizer;
//! correctness of Rust's standard-library implementation remains assumed.

#[cfg(feature = "alloc")]
use alloc::{borrow::Cow, string::String};
#[cfg(feature = "alloc")]
use core::str::{self, Utf8Error};

#[cfg(creusot)]
use crate::form_model;
#[cfg(creusot)]
use creusot_std::prelude::*;

/// A byte trace is valid UTF-8 exactly when it is the UTF-8 encoding of a
/// sequence of Unicode scalar values.
#[cfg(creusot)]
#[logic(open)]
pub(crate) fn utf8_is_valid(bytes: Seq<u8>) -> bool {
    pearlite! { exists<chars: Seq<char>> chars.to_bytes() == bytes }
}

/// Checked pinned UTF-8 step recognizer over integer-valued bytes.
#[cfg(creusot)]
#[logic(open)]
#[requires(0 <= pos && pos < bytes.len())]
pub fn utf8_step(bytes: Seq<Int>, pos: Int) -> (Int, Int, bool) {
    let b0 = bytes[pos];
    let remaining = bytes.len() - pos;
    if 0 <= b0 && b0 <= 127 {
        (b0, 1, true)
    } else if 194 <= b0 && b0 <= 223 {
        if remaining < 2 {
            (65533, remaining, false)
        } else {
            let b1 = bytes[pos + 1];
            if 128 <= b1 && b1 <= 191 {
                ((b0 - 192) * 64 + (b1 - 128), 2, true)
            } else {
                (65533, 1, false)
            }
        }
    } else if 224 <= b0 && b0 <= 239 {
        if remaining < 2 {
            (65533, remaining, false)
        } else {
            let b1 = bytes[pos + 1];
            let second_ok = if b0 == 224 {
                160 <= b1 && b1 <= 191
            } else if b0 == 237 {
                128 <= b1 && b1 <= 159
            } else {
                128 <= b1 && b1 <= 191
            };
            if !second_ok {
                (65533, 1, false)
            } else if remaining < 3 {
                (65533, remaining, false)
            } else {
                let b2 = bytes[pos + 2];
                if 128 <= b2 && b2 <= 191 {
                    ((b0 - 224) * 4096 + (b1 - 128) * 64 + (b2 - 128), 3, true)
                } else {
                    (65533, 2, false)
                }
            }
        }
    } else if 240 <= b0 && b0 <= 244 {
        if remaining < 2 {
            (65533, remaining, false)
        } else {
            let b1 = bytes[pos + 1];
            let second_ok = if b0 == 240 {
                144 <= b1 && b1 <= 191
            } else if b0 == 244 {
                128 <= b1 && b1 <= 143
            } else {
                128 <= b1 && b1 <= 191
            };
            if !second_ok {
                (65533, 1, false)
            } else if remaining < 3 {
                (65533, remaining, false)
            } else {
                let b2 = bytes[pos + 2];
                if !(128 <= b2 && b2 <= 191) {
                    (65533, 2, false)
                } else if remaining < 4 {
                    (65533, remaining, false)
                } else {
                    let b3 = bytes[pos + 3];
                    if 128 <= b3 && b3 <= 191 {
                        (
                            (b0 - 240) * 262144 + (b1 - 128) * 4096 + (b2 - 128) * 64 + (b3 - 128),
                            4,
                            true,
                        )
                    } else {
                        (65533, 3, false)
                    }
                }
            }
        }
    } else {
        (65533, 1, false)
    }
}

/// Prove the progress and bounds property needed by recursive decoding for
/// every sequence whose elements are actual bytes.
#[cfg(creusot)]
#[requires(forall<i: Int> 0 <= i && i < bytes.len() ==> 0 <= bytes[i] && bytes[i] <= 255)]
#[requires(0 <= pos && pos < bytes.len())]
#[ensures({
    let (_, consumed, _) = utf8_step(bytes, pos);
    1 <= consumed && consumed <= bytes.len() - pos
})]
pub(crate) fn utf8_step_bounds(bytes: Seq<Int>, pos: Int) {
    proof_assert!({
        let (_, consumed, _) = utf8_step(bytes, pos);
        1 <= consumed && consumed <= bytes.len() - pos
    });
}

/// First invalid byte offset and Rust's `Utf8Error::error_len` convention.
#[cfg(creusot)]
#[logic(open)]
#[variant(bytes.len())]
pub fn strict_error(bytes: Seq<Int>) -> Option<(Int, Option<Int>)> {
    if bytes.len() == 0 {
        None
    } else {
        let (_, consumed, valid) = utf8_step(bytes, 0);
        if valid {
            match strict_error(bytes.subsequence(consumed, bytes.len())) {
                Some((offset, len)) => Some((consumed + offset, len)),
                None => None,
            }
        } else {
            let lead = bytes[0];
            let remaining = bytes.len();
            let truncated = (194 <= lead && lead <= 223 && remaining < 2)
                || (224 <= lead && lead <= 239 && remaining < 3 && consumed == remaining)
                || (240 <= lead && lead <= 244 && remaining < 4 && consumed == remaining);
            Some((0, if truncated { None } else { Some(consumed) }))
        }
    }
}

#[cfg(creusot)]
#[logic(open)]
pub(crate) fn strict_error_offset(bytes: Seq<Int>) -> Int {
    match strict_error(bytes) {
        Some((offset, _)) => offset,
        None => 0,
    }
}

#[cfg(creusot)]
#[logic(open)]
pub(crate) fn strict_error_length(bytes: Seq<Int>) -> Option<Int> {
    match strict_error(bytes) {
        Some((_, length)) => length,
        None => None,
    }
}

#[cfg(creusot)]
#[logic(open)]
pub(crate) fn utf8_int_valid(bytes: Seq<Int>) -> bool {
    pearlite! {
        exists<raw: Seq<u8>, chars: Seq<char>>
            raw.map(|byte: u8| byte@) == bytes && chars.to_bytes() == raw
    }
}

/// Proof-only edge vectors pin error offsets and lengths around malformed
/// and truncated UTF-8 boundaries. Separate roots keep solver tasks bounded.
#[cfg(creusot)]
pub(crate) fn strict_error_truncated_two() {
    proof_assert!(strict_error(Seq::singleton(195)) == Some((0, None)));
}

#[cfg(creusot)]
pub(crate) fn strict_error_invalid_lead() {
    proof_assert!(strict_error(Seq::singleton(255)) == Some((0, Some(1))));
}

#[cfg(creusot)]
pub(crate) fn strict_error_after_valid_prefix() {
    proof_assert!(
        strict_error(
            Seq::singleton(97)
                .concat(Seq::singleton(195))
                .concat(Seq::singleton(40))
        ) == Some((1, Some(1)))
    );
}

#[cfg(creusot)]
pub(crate) fn strict_error_truncated_after_valid_prefix() {
    proof_assert!(strict_error(Seq::singleton(65).concat(Seq::singleton(195))) == Some((1, None)));
    proof_assert!(
        strict_error(
            Seq::singleton(65)
                .concat(Seq::singleton(226))
                .concat(Seq::singleton(130))
        ) == Some((1, None))
    );
}

#[cfg(creusot)]
pub(crate) fn strict_error_truncated_three() {
    proof_assert!(strict_error(Seq::singleton(226).concat(Seq::singleton(130))) == Some((0, None)));
}

#[cfg(creusot)]
pub(crate) fn strict_error_bad_third_byte() {
    proof_assert!(
        strict_error(
            Seq::singleton(226)
                .concat(Seq::singleton(130))
                .concat(Seq::singleton(65))
        ) == Some((0, Some(2)))
    );
}

#[cfg(creusot)]
pub(crate) fn strict_error_truncated_four() {
    proof_assert!(
        strict_error(
            Seq::singleton(240)
                .concat(Seq::singleton(144))
                .concat(Seq::singleton(128))
        ) == Some((0, None))
    );
}

#[cfg(creusot)]
pub(crate) fn strict_error_bad_fourth_byte() {
    proof_assert!(
        strict_error(
            Seq::singleton(240)
                .concat(Seq::singleton(144))
                .concat(Seq::singleton(128))
                .concat(Seq::singleton(65))
        ) == Some((0, Some(3)))
    );
}

#[cfg(creusot)]
pub(crate) fn strict_error_surrogate() {
    proof_assert!(
        strict_error(
            Seq::singleton(237)
                .concat(Seq::singleton(160))
                .concat(Seq::singleton(128))
        ) == Some((0, Some(1)))
    );
}

#[cfg(creusot)]
pub(crate) fn strict_error_above_unicode_max() {
    proof_assert!(
        strict_error(
            Seq::singleton(244)
                .concat(Seq::singleton(144))
                .concat(Seq::singleton(128))
                .concat(Seq::singleton(128))
        ) == Some((0, Some(1)))
    );
}

#[cfg(creusot)]
pub(crate) fn strict_error_overlong() {
    proof_assert!(
        strict_error(
            Seq::singleton(224)
                .concat(Seq::singleton(128))
                .concat(Seq::singleton(128))
        ) == Some((0, Some(1)))
    );
}

#[cfg(creusot)]
pub(crate) fn strict_error_valid_ascii() {
    proof_assert!(strict_error(Seq::singleton(65).concat(Seq::singleton(66))) == None);
}

#[cfg(creusot)]
pub(crate) fn strict_error_valid_multibyte() {
    proof_assert!(
        strict_error(
            Seq::singleton(226)
                .concat(Seq::singleton(130))
                .concat(Seq::singleton(172))
        ) == None
    );
}

#[cfg(all(feature = "alloc", creusot))]
#[logic(opaque)]
pub(crate) fn std_error_offset(_error: Utf8Error) -> Int {
    dead
}

#[cfg(all(feature = "alloc", creusot))]
#[logic(opaque)]
pub(crate) fn std_error_length(_error: Utf8Error) -> Option<Int> {
    dead
}

#[cfg(all(feature = "alloc", creusot))]
#[logic(open)]
pub(crate) fn cow_bytes(value: Cow<'_, [u8]>) -> Seq<u8> {
    pearlite! {
        match value {
            Cow::Borrowed(bytes) => bytes@,
            Cow::Owned(bytes) => bytes@,
        }
    }
}

#[cfg(all(feature = "alloc", creusot))]
#[logic(open, prophetic)]
pub(crate) fn lossy_bytes_relation(bytes: Seq<u8>, output: Seq<Int>) -> bool {
    pearlite! {
        exists<raw: &[u8], decoded: Cow<'_, str>>
            raw@ == bytes
                && String::from_utf8_lossy.postcondition((raw,), decoded)
                && form_model::cow_str_scalars(decoded) == output
    }
}

#[cfg(all(feature = "alloc", creusot))]
#[logic(open, prophetic)]
pub(crate) fn lossy_int_relation(bytes: Seq<Int>, output: Seq<Int>) -> bool {
    pearlite! {
        exists<raw: &[u8], decoded: Cow<'_, str>>
            form_model::byte_sequence_as_ints(raw@) == bytes
                && String::from_utf8_lossy.postcondition((raw,), decoded)
                && form_model::cow_str_scalars(decoded) == output
    }
}

#[cfg(all(feature = "alloc", creusot))]
extern_spec! {
    mod core {
        mod str {
            #[ensures(match result {
                Ok(value) => utf8_is_valid(bytes@)
                    && utf8_int_valid(form_model::byte_sequence_as_ints(bytes@))
                    && exists<chars: Seq<char>>
                        chars.to_bytes() == bytes@ && value@ == chars,
                Err(error) => !utf8_is_valid(bytes@)
                    && !utf8_int_valid(form_model::byte_sequence_as_ints(bytes@))
                    && std_error_offset(error)
                        == strict_error_offset(form_model::byte_sequence_as_ints(bytes@))
                    && std_error_length(error)
                        == strict_error_length(form_model::byte_sequence_as_ints(bytes@)),
            })]
            fn from_utf8(bytes: &[u8]) -> Result<&str, Utf8Error>;
        }
    }

    impl Utf8Error {
        #[ensures(result@ == std_error_offset(*self))]
        fn valid_up_to(&self) -> usize;

        #[ensures(match result {
            Some(length) => Some(length@),
            None => None,
        } == std_error_length(*self))]
        fn error_len(&self) -> Option<usize>;
    }

}

/// Strictly decode bytes while retaining borrowed versus owned storage.
///
/// The postcondition models result validity, successful contents, the Cow
/// variant selected from input ownership, and exact `Utf8Error` detail fields.
#[cfg(feature = "alloc")]
#[cfg_attr(creusot, ensures(match result {
    Ok(Cow::Borrowed(value)) => match input {
        Cow::Borrowed(bytes) => utf8_int_valid(form_model::byte_sequence_as_ints(bytes@))
            && exists<chars: Seq<char>>
                chars.to_bytes() == bytes@ && value@ == chars,
        Cow::Owned(_) => false,
    },
    Ok(Cow::Owned(value)) => match input {
        Cow::Borrowed(_) => false,
        Cow::Owned(bytes) => utf8_int_valid(form_model::byte_sequence_as_ints(bytes@))
            && exists<chars: Seq<char>>
                chars.to_bytes() == bytes@ && value@ == chars,
    },
    Err(error) => !utf8_is_valid(cow_bytes(input))
        && !utf8_int_valid(form_model::byte_sequence_as_ints(cow_bytes(input)))
        && std_error_offset(error)
            == strict_error_offset(form_model::byte_sequence_as_ints(cow_bytes(input)))
        && std_error_length(error)
            == strict_error_length(form_model::byte_sequence_as_ints(cow_bytes(input))),
}))]
pub(crate) fn decode_utf8(input: Cow<'_, [u8]>) -> Result<Cow<'_, str>, Utf8Error> {
    match input {
        Cow::Borrowed(bytes) => match str::from_utf8(bytes) {
            Ok(value) => Ok(Cow::Borrowed(value)),
            Err(error) => Err(error),
        },
        Cow::Owned(bytes) => {
            let raw: &[u8] = &bytes;
            match str::from_utf8(raw) {
                Ok(_value) => {
                    #[cfg(creusot)]
                    proof_assert!(utf8_is_valid(bytes@));
                    Ok(Cow::Owned(unsafe { String::from_utf8_unchecked(bytes) }))
                }
                Err(error) => Err(error),
            }
        }
    }
}

/// Lossily decode bytes, reusing an owned vector when the input is valid UTF-8.
#[cfg(feature = "alloc")]
#[cfg_attr(
    creusot,
    ensures(lossy_bytes_relation(cow_bytes(input), form_model::cow_str_scalars(result)))
)]
#[cfg_attr(creusot, ensures(match input {
    Cow::Borrowed(bytes) => String::from_utf8_lossy.postcondition((bytes,), result),
    Cow::Owned(_) => match result {
        Cow::Borrowed(_) => false,
        Cow::Owned(_) => true,
    },
}))]
pub(crate) fn decode_utf8_lossy(input: Cow<'_, [u8]>) -> Cow<'_, str> {
    match input {
        Cow::Borrowed(bytes) => String::from_utf8_lossy(bytes),
        Cow::Owned(bytes) => {
            #[cfg(creusot)]
            let raw: &[u8] = &bytes;
            let decoded = String::from_utf8_lossy(&bytes);
            #[cfg(creusot)]
            {
                proof_assert!(String::from_utf8_lossy.postcondition((raw,), decoded));
                proof_assert!(lossy_bytes_relation(bytes@, form_model::cow_str_scalars(decoded)));
            }
            match decoded {
                Cow::Borrowed(utf8) => {
                    // Check that the validated string retains the input bytes in debug builds.
                    debug_assert_eq!(utf8.as_bytes(), &*bytes);
                    #[cfg(creusot)]
                    proof_assert!({
                        creusot_std::std::string::injective_to_bytes();
                        true
                    });
                    Cow::Owned(unsafe { String::from_utf8_unchecked(bytes) })
                }
                Cow::Owned(string) => Cow::Owned(string),
            }
        }
    }
}
