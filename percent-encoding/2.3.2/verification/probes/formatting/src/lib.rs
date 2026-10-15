#![no_std]

use core::fmt::{self, Formatter};
#[cfg(creusot)]
use creusot_std::prelude::*;

#[cfg(creusot)]
use form_model;

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

#[path = "../../../../crate/src/format_trace.rs"]
mod format_trace;

#[cfg(creusot)]
#[path = "../../../../crate/src/encode_models.rs"]
mod encode_models;

#[path = "../../../../crate/src/encoder_display.rs"]
mod encoder_display;

pub use percent_encoding::PercentEncode;

#[cfg(creusot)]
use format_trace::{failed_prefix, request_write, successful_prefix};

// Translation probe: a loop writing only static ASCII literals. The library
// model gives Formatter::write_str no contract, so this deliberately makes no
// claim about bytes accepted by the supplied formatter.
#[cfg(creusot)]
pub fn literal_loop(f: &mut Formatter<'_>, count: u8) -> fmt::Result {
    let mut i = 0;
    #[invariant(i <= count)]
    while i < count {
        f.write_str("x")?;
        i += 1;
    }
    Ok(())
}

// Translation probe for the standard formatting macro and its dynamic Debug
// dispatch, with a scalar numeric argument.
#[cfg(creusot)]
pub fn numeric_format(f: &mut Formatter<'_>, value: u8) -> fmt::Result {
    fmt::Display::fmt(&value, f)
}

#[cfg(creusot)]
pub fn macro_numeric_format(f: &mut Formatter<'_>, value: u8) -> fmt::Result {
    write!(f, "{}", value)
}

// Derived Debug calls exercise Formatter builder methods and trait objects.
#[derive(Debug)]
pub struct DebugPayload(pub u8);

#[cfg(creusot)]
pub fn derived_debug(f: &mut Formatter<'_>, value: &DebugPayload) -> fmt::Result {
    fmt::Debug::fmt(value, f)
}

#[cfg(creusot)]
pub fn pair_trace(f: &mut Formatter<'_>, left: &str, right: &str) -> fmt::Result {
    let chunks = [left, right];
    let mut trace = Seq::new();
    let mut i = 0;
    #[invariant(0 <= i@ && i@ <= chunks@.len())]
    #[invariant(successful_prefix(chunks@, *trace, i@))]
    while i < chunks.len() {
        let chunk = chunks[i];
        match request_write(f, chunk, trace.borrow_mut()) {
            Err(error) => {
                proof_assert!(failed_prefix(chunks@, *trace, i@));
                return Err(error);
            }
            Ok(()) => i += 1,
        }
    }
    Ok(())
}

#[cfg(creusot)]
pub fn encoded_pair_trace(
    f: &mut Formatter<'_>,
    left: &str,
    right: &str,
) -> fmt::Result {
    use format_trace::{failed_model_prefix, request_write, successful_model_prefix};

    let chunks = [left, right];
    let mut trace = Seq::new();
    let mut i = 0;
    #[invariant(i@ <= chunks@.len())]
    #[invariant(successful_model_prefix(
        Seq::singleton(form_model::string_chunk_bytes(left))
            .concat(Seq::singleton(form_model::string_chunk_bytes(right))),
        *trace, i@,
    ))]
    while i < chunks.len() {
        let chunk = chunks[i];
        match request_write(f, chunk, trace.borrow_mut()) {
            Err(error) => {
                proof_assert!(failed_model_prefix(
                    Seq::singleton(form_model::string_chunk_bytes(left))
                        .concat(Seq::singleton(form_model::string_chunk_bytes(right))),
                    *trace, i@,
                ));
                return Err(error);
            }
            Ok(()) => i += 1,
        }
    }
    proof_assert!(successful_model_prefix(
        Seq::singleton(form_model::string_chunk_bytes(left))
            .concat(Seq::singleton(form_model::string_chunk_bytes(right))),
        *trace, i@,
    ));
    Ok(())
}

pub fn display_any(f: &mut Formatter<'_>, bytes: &[u8]) -> fmt::Result {
    let encoder = percent_encoding::percent_encode(bytes, percent_encoding::NON_ALPHANUMERIC);
    encoder_display::format_encoder(&encoder, f)
}

#[cfg(not(creusot))]
pub fn native_write(f: &mut Formatter<'_>, chunk: &str) -> fmt::Result {
    format_trace::request_write(f, chunk)
}
