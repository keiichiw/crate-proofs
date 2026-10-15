#![no_std]

extern crate alloc;

use alloc::borrow::Cow;
#[cfg(creusot)]
use creusot_std::prelude::*;

pub type EncodingOverride<'a> = Option<&'a dyn Fn(&str) -> Cow<'_, [u8]>>;

pub struct Probe<'a> {
    callback: EncodingOverride<'a>,
}

impl<'a> Probe<'a> {
    pub fn new() -> Self {
        Self { callback: None }
    }

    pub fn set(&mut self, callback: EncodingOverride<'a>) {
        self.callback = callback;
    }

    pub fn call<'b>(&self, input: &'b str) -> Option<Cow<'b, [u8]>> {
        self.callback.map(|callback| callback(input))
    }
}

pub fn identity(input: &str) -> Cow<'_, [u8]> {
    Cow::Borrowed(input.as_bytes())
}

#[cfg(creusot)]
pub fn exercise(input: &str) -> Option<Cow<'_, [u8]>> {
    let mut probe = Probe::new();
    probe.set(Some(&identity));
    probe.call(input)
}
