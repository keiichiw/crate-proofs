#![no_std]

#[path = "../../../../crate/src/ascii_set.rs"]
mod ascii_set;
pub use ascii_set::AsciiSet;

#[path = "../../../../crate/src/debug_trace.rs"]
mod debug_trace;

use core::fmt::{self, Formatter};
#[cfg(creusot)]
use creusot_std::prelude::*;

#[cfg(creusot)]
pub fn trace_mask(formatter: &mut Formatter<'_>, mask: &[u32; 4]) -> fmt::Result {
    let struct_name = "AsciiSet";
    let field_name = "mask";
    let mut trace = debug_trace::DebugTrace::empty(struct_name);
    let mut builder = debug_trace::start(formatter, struct_name, trace.borrow_mut());
    debug_trace::field_words(&mut builder, field_name, mask, trace.borrow_mut());
    let result = debug_trace::finish(&mut builder, trace.borrow_mut());
    proof_assert!(trace.struct_name == struct_name);
    proof_assert!(trace.field_names.len() == 1);
    proof_assert!(trace.field_names[0] == field_name);
    proof_assert!(trace.field_type_tags[0] == 0u8);
    proof_assert!(trace.byte_values.len() == 0);
    proof_assert!(trace.iter_values.len() == 0);
    proof_assert!(trace.ascii_set_values.len() == 0);
    proof_assert!(trace.word_values.len() == 1);
    proof_assert!(*trace.word_values[0] == mask@);
    proof_assert!(
        trace.finish_status
            == Some(match result {
                Ok(()) => true,
                Err(_) => false,
            })
    );
    result
}

#[cfg(creusot)]
pub fn trace_encoder(
    formatter: &mut Formatter<'_>,
    bytes: &[u8],
    ascii_set: &AsciiSet,
) -> fmt::Result {
    let struct_name = "PercentEncode";
    let bytes_field_name = "bytes";
    let ascii_set_field_name = "ascii_set";
    let mut trace = debug_trace::DebugTrace::empty(struct_name);
    let mut builder = debug_trace::start(formatter, struct_name, trace.borrow_mut());
    debug_trace::field_bytes(&mut builder, bytes_field_name, bytes, trace.borrow_mut());
    debug_trace::field_ascii_set(
        &mut builder,
        ascii_set_field_name,
        ascii_set,
        trace.borrow_mut(),
    );
    let result = debug_trace::finish(&mut builder, trace.borrow_mut());
    proof_assert!(trace.struct_name == struct_name);
    proof_assert!(trace.field_names.len() == 2);
    proof_assert!(trace.field_names[0] == bytes_field_name);
    proof_assert!(trace.field_names[1] == ascii_set_field_name);
    proof_assert!(trace.field_type_tags[0] == 1u8);
    proof_assert!(trace.field_type_tags[1] == 3u8);
    proof_assert!(trace.byte_values.len() == 1);
    proof_assert!(*trace.byte_values[0] == bytes@);
    proof_assert!(trace.word_values.len() == 0);
    proof_assert!(trace.iter_values.len() == 0);
    proof_assert!(trace.ascii_set_values.len() == 1);
    proof_assert!(*trace.ascii_set_values[0] == ascii_set.mask_words());
    proof_assert!(
        trace.finish_status
            == Some(match result {
                Ok(()) => true,
                Err(_) => false,
            })
    );
    result
}

#[cfg(creusot)]
pub fn trace_decoder(formatter: &mut Formatter<'_>, bytes: &[u8]) -> fmt::Result {
    let mut iter = bytes.iter();
    let _ = iter.next();
    let struct_name = "PercentDecode";
    let field_name = "bytes";
    let mut trace = debug_trace::DebugTrace::empty(struct_name);
    let mut builder = debug_trace::start(formatter, struct_name, trace.borrow_mut());
    debug_trace::field_byte_iter(&mut builder, field_name, &iter, trace.borrow_mut());
    let result = debug_trace::finish(&mut builder, trace.borrow_mut());
    proof_assert!(trace.struct_name == struct_name);
    proof_assert!(trace.field_names.len() == 1);
    proof_assert!(trace.field_names[0] == field_name);
    proof_assert!(trace.field_type_tags[0] == 2u8);
    proof_assert!(trace.word_values.len() == 0);
    proof_assert!(trace.byte_values.len() == 0);
    proof_assert!(trace.iter_values.len() == 1);
    proof_assert!(*trace.iter_values[0] == iter@@);
    proof_assert!(trace.ascii_set_values.len() == 0);
    proof_assert!(
        trace.finish_status
            == Some(match result {
                Ok(()) => true,
                Err(_) => false,
            })
    );
    result
}
