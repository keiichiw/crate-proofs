#![no_std]

extern crate alloc;

#[cfg(creusot)]
use alloc::{borrow::Cow, string::String, vec::Vec};
#[cfg(creusot)]
use core::str::{self, Utf8Error};
#[cfg(creusot)]
use creusot_std::prelude::*;

#[cfg(creusot)]
#[logic(open)]
pub fn utf8_valid(bytes: Seq<u8>) -> bool {
    pearlite! {
        exists<chars: Seq<char>> chars.to_bytes() == bytes
    }
}

#[cfg(creusot)]
#[logic(open)]
pub fn cow_bytes(value: Cow<'_, [u8]>) -> Seq<u8> {
    pearlite! {
        match value {
            Cow::Borrowed(bytes) => bytes@,
            Cow::Owned(bytes) => bytes@,
        }
    }
}

#[cfg(creusot)]
extern_spec! {
    mod core {
        mod str {
            #[ensures(match result {
                Ok(value) => utf8_valid(bytes@)
                    && exists<chars: Seq<char>>
                        chars.to_bytes() == bytes@
                            && value@ == chars,
                Err(_) => !utf8_valid(bytes@),
            })]
            fn from_utf8(bytes: &[u8]) -> Result<&str, Utf8Error>;
        }
    }

    impl String {
        #[ensures(match result {
            Ok(value) => utf8_valid(bytes@)
                && exists<chars: Seq<char>>
                    chars.to_bytes() == bytes@
                        && value@ == chars,
            Err(_) => !utf8_valid(bytes@),
        })]
        fn from_utf8(bytes: Vec<u8>) -> Result<String, alloc::string::FromUtf8Error>;
    }

    impl alloc::string::FromUtf8Error {
        #[ensures(true)]
        fn utf8_error(&self) -> Utf8Error;
    }
}

#[cfg(creusot)]
#[ensures(match result {
    Ok(Cow::Borrowed(value)) => exists<chars: Seq<char>>
        chars.to_bytes() == cow_bytes(input)
            && value@ == chars
            && match input { Cow::Borrowed(_) => true, Cow::Owned(_) => false },
    Ok(Cow::Owned(value)) => exists<chars: Seq<char>>
        chars.to_bytes() == cow_bytes(input)
            && value@ == chars
            && match input { Cow::Borrowed(_) => false, Cow::Owned(_) => true },
    Err(_) => !utf8_valid(cow_bytes(input)),
})]
pub fn strict_cow_decode(input: Cow<'_, [u8]>) -> Result<Cow<'_, str>, Utf8Error> {
    match input {
        Cow::Borrowed(bytes) => match str::from_utf8(bytes) {
            Ok(value) => Ok(Cow::Borrowed(value)),
            Err(error) => Err(error),
        },
        Cow::Owned(bytes) => {
            let byte_trace = snapshot!(bytes@);
            match String::from_utf8(bytes) {
                Ok(value) => Ok(Cow::Owned(value)),
                Err(error) => {
                    proof_assert!(!utf8_valid(*byte_trace));
                    Err(error.utf8_error())
                }
            }
        }
    }
}
