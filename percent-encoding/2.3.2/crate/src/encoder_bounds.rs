//! Checked size bounds for the encoder's chunk sequence.
//!
//! This supplements, but does not alter, the chunk recurrence in
//! `encode_models`. Each nonempty input step emits one chunk, then recurses
//! either on one fewer escaped byte or after a nonempty unchanged run.

#[cfg(creusot)]
use creusot_std::prelude::*;

#[cfg(creusot)]
use crate::encode_models;

/// Prove that encoded chunk count is zero exactly for empty input and is
/// otherwise between one and the input byte length.
#[cfg(creusot)]
#[logic(opaque)]
#[variant(input.len())]
#[requires(mask.len() == 4)]
#[ensures(result)]
#[ensures(encode_models::encoded_chunks(mask, input).len() <= input.len())]
#[ensures((input.len() == 0) == (encode_models::encoded_chunks(mask, input).len() == 0))]
#[ensures(input.len() > 0 ==> encode_models::encoded_chunks(mask, input).len() >= 1)]
pub(crate) fn encoded_chunk_count_bounds(mask: Seq<u32>, input: Seq<u8>) -> bool {
    pearlite! {
        if input.len() == 0 {
            true
        } else if encode_models::should_encode_model(mask, input[0]) {
            let tail = input.subsequence(1, input.len());
            encode_models::encoded_chunks_first_escaped(mask, input)
                && encoded_chunk_count_bounds(mask, tail)
        } else {
            let end = encode_models::safe_run_end(input, 0, mask);
            let tail = input.subsequence(end, input.len());
            encode_models::encoded_chunks_first_run(mask, input, end)
                && encoded_chunk_count_bounds(mask, tail)
        }
    }
}
