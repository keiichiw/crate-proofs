#![no_std]

extern crate alloc;

#[cfg(creusot)]
#[path = "../../../../crate/src/stdlib_models.rs"]
mod stdlib_models;

#[cfg(creusot)]
use alloc::borrow::Cow;
#[cfg(creusot)]
use alloc::string::String;
#[cfg(creusot)]
use alloc::vec::Vec;
#[cfg(creusot)]
use creusot_std::prelude::*;

/// Translation probe for the modeled library entry point and its Cow variants.
#[cfg(creusot)]
pub fn lossy(bytes: &[u8]) -> Cow<'_, str> {
    String::from_utf8_lossy(bytes)
}

#[cfg(creusot)]
pub fn as_bytes(s: &str) -> &[u8] {
    s.as_bytes()
}

#[cfg(creusot)]
pub unsafe fn from_utf8_unchecked(bytes: &[u8]) -> &str {
    core::str::from_utf8_unchecked(bytes)
}

#[cfg(creusot)]
pub fn split_first<T>(xs: &[T]) -> Option<(&T, &[T])> {
    xs.split_first()
}

#[cfg(creusot)]
pub fn split_at<T>(xs: &[T], mid: usize) -> (&[T], &[T]) {
    xs.split_at(mid)
}

#[cfg(creusot)]
pub fn push_str(mut s: String, suffix: &str) -> String {
    s.push_str(suffix);
    s
}

#[cfg(creusot)]
pub fn truncate(mut s: String, boundary: usize) -> String {
    s.truncate(boundary);
    s
}

#[cfg(creusot)]
#[ensures(result@ == input@)]
pub fn copy(input: &[u8]) -> Vec<u8> {
    input.to_vec()
}

