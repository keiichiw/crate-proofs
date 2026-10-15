//! Checked recurrence helpers for the percent-decoder's decoded-byte model.

#[cfg(creusot)]
use creusot_std::prelude::*;
#[cfg(creusot)]
use form_model;

/// Mapping a byte concatenation to integers preserves concatenation.
#[cfg(creusot)]
#[logic(opaque)]
#[ensures(result)]
#[ensures(form_model::byte_sequence_as_ints(left.concat(right))
    == form_model::byte_sequence_as_ints(left)
        .concat(form_model::byte_sequence_as_ints(right)))]
pub(crate) fn byte_map_concat(left: Seq<u8>, right: Seq<u8>) -> bool {
    true
}

/// The tail of a mapped suffix is the mapping of the correspondingly shifted
/// suffix. This isolates the nested-slice arithmetic at decoder loop steps.
#[cfg(creusot)]
#[logic(opaque)]
#[requires(0 <= start && start < bytes.len())]
#[ensures(result)]
#[ensures(form_model::byte_sequence_as_ints(bytes.subsequence(start, bytes.len()))
        .subsequence(1, bytes.len() - start)
    == form_model::byte_sequence_as_ints(bytes.subsequence(start + 1, bytes.len())))]
pub(crate) fn byte_map_nested_tail(bytes: Seq<u8>, start: Int) -> bool {
    form_model::byte_model_subsequence(bytes, start, bytes.len());
    form_model::byte_model_subsequence(bytes, start + 1, bytes.len());
    form_model::byte_model_subsequence(bytes.subsequence(start, bytes.len()), 1, bytes.len() - start);
    true
}

/// Reassociate the model prefix, a newly emitted chunk, and its remaining
/// decoded suffix.
#[cfg(creusot)]
#[logic(opaque)]
#[ensures(result)]
#[ensures(left.concat(middle.concat(right))
    == left.concat(middle).concat(right))]
pub(crate) fn concat_assoc<T>(left: Seq<T>, middle: Seq<T>, right: Seq<T>) -> bool {
    let _ = Seq::<T>::concat_assoc;
    true
}

/// Mapping a prefix extended by one byte equals the mapped prefix followed by
/// that byte's integer value.
#[cfg(creusot)]
#[logic(opaque)]
#[requires(0 <= index && index < bytes.len())]
#[ensures(result)]
#[ensures(form_model::byte_sequence_as_ints(bytes).subsequence(0, index + 1)
    == form_model::byte_sequence_as_ints(bytes).subsequence(0, index)
        .concat(Seq::singleton(bytes[index]@)))]
pub(crate) fn byte_map_prefix_push(bytes: Seq<u8>, index: Int) -> bool {
    form_model::byte_int_prefix_push(bytes, index);
    true
}

/// The byte-model of appending one byte is the old model followed by that byte.
#[cfg(creusot)]
#[logic(opaque)]
#[ensures(result)]
#[ensures(form_model::byte_sequence_as_ints(bytes.push_back(byte))
    == form_model::byte_sequence_as_ints(bytes).concat(Seq::singleton(byte@)))]
pub(crate) fn byte_map_push_back(bytes: Seq<u8>, byte: u8) -> bool {
    byte_map_concat(bytes, Seq::singleton(byte));
    true
}

/// The model emits the first byte unchanged when it is not a valid escape.
#[cfg(creusot)]
#[logic(opaque)]
#[requires(input.len() > 0)]
#[requires(!(input.len() >= 3 && input[0] == 37
    && form_model::percent_hex_value_model(input[1]) >= 0
    && form_model::percent_hex_value_model(input[2]) >= 0))]
#[ensures(result)]
#[ensures(crate::decoded_trace(input)
    == Seq::singleton(input[0]).concat(
        crate::decoded_trace(input.subsequence(1, input.len()))
    ))]
pub(crate) fn decoded_trace_plain_step(input: Seq<Int>) -> bool {
    true
}

/// The model emits one decoded byte for a valid `%HH` triplet.
#[cfg(creusot)]
#[logic(opaque)]
#[requires(input.len() >= 3)]
#[requires(input[0] == 37)]
#[requires(form_model::percent_hex_value_model(input[1]) >= 0)]
#[requires(form_model::percent_hex_value_model(input[2]) >= 0)]
#[ensures(result)]
#[ensures(crate::decoded_trace(input)
    == Seq::singleton(
        form_model::percent_hex_value_model(input[1]) * 16
            + form_model::percent_hex_value_model(input[2]),
    ).concat(crate::decoded_trace(input.subsequence(3, input.len()))))]
pub(crate) fn decoded_trace_escape_step(input: Seq<Int>) -> bool {
    true
}
