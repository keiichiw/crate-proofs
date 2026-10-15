//! Reviewed models for the UTF-8 standard-library boundary used by decode.
//!
//! The model below is an explicit UTF-8 recognizer and lossy decoder over
//! integer-valued bytes. The UTF-8 classification and replacement-consumption
//! rules are checked ghost definitions. Standard-library contracts in the
//! extern-spec section state the exact content and mutation boundaries used by
//! the crate; `String::from_utf8_lossy` carries the lossy-conversion model.

use alloc::borrow::Cow;
use alloc::string::String;
use creusot_std::prelude::*;

/// Decode the UTF-8 sequence beginning at `pos` in an integer-byte trace.
///
/// The tuple contains `(scalar, consumed_bytes, valid_sequence)`.  For malformed
/// input, `consumed_bytes` is the length of the valid prefix before the offending
/// byte, or all remaining bytes when that prefix is truncated at EOF.  This is
/// the maximal-subpart rule used by Rust's lossy conversion. Values outside
/// `0..=255` are totalized as invalid single-byte units; std slice inputs are
/// mapped from `u8` and therefore never use this extension.
#[logic(open)]
#[requires(0 <= pos && pos < bytes.len())]
#[ensures(1 <= result.1 && result.1 <= bytes.len() - pos)]
#[ensures(result.0 == 65533 || (0 <= result.0 && result.0 <= 55295)
    || (57344 <= result.0 && result.0 <= 1114111))]
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
                        ((b0 - 240) * 262144 + (b1 - 128) * 4096
                            + (b2 - 128) * 64 + (b3 - 128), 4, true)
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

/// Exact scalar sequence produced by Rust's lossy UTF-8 conversion.
#[logic(open)]
#[variant(bytes.len())]
pub fn utf8_lossy_model(bytes: Seq<Int>) -> Seq<Int> {
    if bytes.len() == 0 {
        Seq::empty()
    } else {
        let (scalar, consumed, _) = utf8_step(bytes, 0);
        Seq::singleton(scalar).concat(utf8_lossy_model(
            bytes.subsequence(consumed, bytes.len()),
        ))
    }
}

/// Whether all input bytes form complete, canonical UTF-8 scalar encodings.
#[logic(open)]
#[variant(bytes.len())]
pub fn utf8_is_valid(bytes: Seq<Int>) -> bool {
    if bytes.len() == 0 {
        true
    } else {
        let (_, consumed, valid) = utf8_step(bytes, 0);
        valid && utf8_is_valid(bytes.subsequence(consumed, bytes.len()))
    }
}

#[logic(open, inline)]
fn chars_as_scalars(chars: Seq<char>) -> Seq<Int> {
    pearlite! { chars.map(|c: char| c@) }
}

extern_spec! {
    impl str {
        // `as_bytes` exposes the UTF-8 encoding represented by the `str`
        // model.  This is a content contract only; it carries no promise
        // about pointer provenance or raw-pointer identity.
        #[ensures(result@ == self@.to_bytes())]
        fn as_bytes(&self) -> &[u8];

    }

    impl<T> [T] {
        #[ensures(match result {
            Some((first, tail)) => self@.len() > 0
                && *first == self@[0]
                && tail@ == self@.tail(),
            None => self@ == Seq::empty(),
        })]
        fn split_first(&self) -> Option<(&T, &[T])>;

        #[requires(mid@ <= self@.len())]
        #[ensures({
            let (left, right) = result;
            left@ == self@.subsequence(0, mid@)
                && right@ == self@.subsequence(mid@, self@.len())
        })]
        fn split_at(&self, mid: usize) -> (&[T], &[T]);
    }

    impl String {
        // The lossy conversion's content relation is exact for all byte
        // sequences; the variant relation captures the borrowed fast path.
        #[ensures(match result {
            Cow::Borrowed(s) => utf8_is_valid(bytes@.map(|b: u8| b@))
                && chars_as_scalars(s@) == utf8_lossy_model(bytes@.map(|b: u8| b@))
                && s@.to_bytes() == bytes@,
            Cow::Owned(s) => !utf8_is_valid(bytes@.map(|b: u8| b@))
                && chars_as_scalars(s@) == utf8_lossy_model(bytes@.map(|b: u8| b@)),
        })]
        fn from_utf8_lossy(bytes: &[u8]) -> Cow<'_, str>;

        // `String` mutators are modeled at the character-sequence level,
        // matching the standard library's string model.
        #[ensures((^self)@ == self@.concat(string@))]
        fn push_str(&mut self, string: &str);

        // `truncate` is a no-op when the requested byte length is at least the
        // current length.  Below that length, it returns normally only at a
        // UTF-8 character boundary; an interior byte offset panics.
        #[requires(new_len@ >= self@.to_bytes().len()
            || exists<prefix: Seq<char>, suffix: Seq<char>>
                self@ == prefix.concat(suffix)
                    && prefix.to_bytes().len() == new_len@)]
        #[ensures(if new_len@ >= self@.to_bytes().len() {
            (^self)@ == self@
        } else {
            exists<prefix: Seq<char>, suffix: Seq<char>>
                self@ == prefix.concat(suffix)
                    && prefix.to_bytes().len() == new_len@
                    && (^self)@ == prefix
        })]
        fn truncate(&mut self, new_len: usize);
    }

}

extern_spec! {
    mod core {
        mod str {
            // The caller must establish UTF-8 validity.  The result is the
            // same string viewed through Rust's scalar model, encoded as
            // these bytes.
            #[requires((forall<i: Int> 0 <= i && i < bytes@.len()
                    ==> bytes@[i]@ < 128)
                || exists<s: Seq<char>> s.to_bytes() == bytes@)]
            #[ensures(result@.to_bytes() == bytes@)]
            unsafe fn from_utf8_unchecked(bytes: &[u8]) -> &str;
        }
    }
}
