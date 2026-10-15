#![no_std]

extern crate alloc;

#[cfg(creusot)]
use alloc::{borrow::Cow, string::String};
#[cfg(creusot)]
use creusot_std::prelude::*;
#[cfg(creusot)]
use form_model;

/// Relate a scalar trace to the inherited standard-library lossy UTF-8 model.
#[cfg(creusot)]
#[logic(open, prophetic)]
pub fn lossy_relation(input: &[u8], output: Seq<Int>) -> bool {
    pearlite! {
        exists<c: Cow<'_, str>>
            String::from_utf8_lossy.postcondition((input,), c)
                && form_model::cow_str_scalars(c) == output
    }
}

/// Probe whether the public function contract can use that relation directly.
#[cfg(creusot)]
#[ensures(lossy_relation(input, form_model::cow_str_scalars(result)))]
pub fn std_lossy_probe(input: &[u8]) -> Cow<'_, str> {
    String::from_utf8_lossy(input)
}

#[cfg(creusot)]
#[logic(open)]
pub fn cow_bytes(input: Cow<'_, [u8]>) -> Seq<u8> {
    pearlite! {
        match input {
            Cow::Borrowed(bytes) => bytes@,
            Cow::Owned(bytes) => bytes@,
        }
    }
}

/// Existentially connect an input byte trace to the inherited lossy std model.
#[cfg(creusot)]
#[logic(open, prophetic)]
pub fn lossy_bytes_relation(bytes: Seq<u8>, output: Seq<Int>) -> bool {
    pearlite! {
        exists<raw: &[u8], c: Cow<'_, str>>
            raw@ == bytes
                && String::from_utf8_lossy.postcondition((raw,), c)
                && form_model::cow_str_scalars(c) == output
    }
}

/// Reproduce the form crate's Cow-aware lossy decoder in isolation.
#[cfg(creusot)]
#[ensures(lossy_bytes_relation(cow_bytes(input), form_model::cow_str_scalars(result)))]
#[ensures(match input {
    Cow::Borrowed(bytes) => String::from_utf8_lossy.postcondition((bytes,), result),
    Cow::Owned(_) => match result {
        Cow::Borrowed(_) => false,
        Cow::Owned(_) => true,
    },
})]
pub fn cow_lossy_decode(input: Cow<'_, [u8]>) -> Cow<'_, str> {
    match input {
        Cow::Borrowed(bytes) => String::from_utf8_lossy(bytes),
        Cow::Owned(bytes) => {
            let raw: &[u8] = &bytes;
            let decoded = String::from_utf8_lossy(&bytes);
            proof_assert!(String::from_utf8_lossy.postcondition((raw,), decoded));
            proof_assert!(lossy_bytes_relation(bytes@, form_model::cow_str_scalars(decoded)));
            match decoded {
                Cow::Borrowed(utf8) => {
                    debug_assert_eq!(utf8.as_bytes(), &*bytes);
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
