#![no_std]

extern crate alloc;

#[path = "../../../../crate/src/utf8_models.rs"]
#[allow(dead_code)]
mod utf8_models;

#[cfg(creusot)]
use alloc::borrow::Cow;
#[cfg(creusot)]
use core::str::Utf8Error;
#[cfg(creusot)]
use creusot_std::prelude::*;
#[cfg(creusot)]
use form_model;

#[cfg(creusot)]
#[ensures(match result {
    Ok(Cow::Borrowed(value)) => match input {
        Cow::Borrowed(bytes) => exists<chars: Seq<char>>
            chars.to_bytes() == bytes@ && value@ == chars,
        Cow::Owned(_) => false,
    },
    Ok(Cow::Owned(value)) => match input {
        Cow::Borrowed(_) => false,
        Cow::Owned(bytes) => exists<chars: Seq<char>>
            chars.to_bytes() == bytes@ && value@ == chars,
    },
    Err(_) => !utf8_models::utf8_is_valid(utf8_models::cow_bytes(input)),
})]
pub fn strict_decode(input: Cow<'_, [u8]>) -> Result<Cow<'_, str>, Utf8Error> {
    utf8_models::decode_utf8(input)
}

#[cfg(creusot)]
#[ensures(utf8_models::lossy_bytes_relation(
    utf8_models::cow_bytes(input),
    form_model::cow_str_scalars(result)
))]
pub fn lossy_decode(input: Cow<'_, [u8]>) -> Cow<'_, str> {
    utf8_models::decode_utf8_lossy(input)
}
