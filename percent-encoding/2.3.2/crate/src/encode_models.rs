//! Logical model of the public percent encoder's output chunks.
//!
//! This module describes the maximal unchanged runs and individual `%HH`
//! escapes emitted by the encoder. It does not change or replace runtime code.

#[cfg(creusot)]
use creusot_std::prelude::*;

/// Whether an input byte is selected by the four-word ASCII mask.
/// Non-ASCII bytes are always encoded, matching `AsciiSet::should_percent_encode`.
#[cfg(creusot)]
#[logic(open)]
#[bitwise_proof]
pub fn should_encode_model(mask: Seq<u32>, byte: u8) -> bool {
    pearlite! {
        byte@ >= 128 || mask[byte@ / 32] & (1u32 << (byte & 31u8)) != 0u32
    }
}

/// End of the maximal unchanged run beginning at `start`.
/// The caller supplies an in-bounds start and a four-word mask.
#[cfg(creusot)]
#[logic(opaque)]
#[variant(input.len() - start)]
#[requires(0 <= start && start <= input.len())]
#[requires(mask.len() == 4)]
#[ensures(start <= result && result <= input.len())]
#[ensures(pearlite! { forall<i: Int> start <= i && i < result
    ==> !should_encode_model(mask, input[i]) })]
#[ensures(result == input.len() || should_encode_model(mask, input[result]))]
#[ensures(start < input.len() && !should_encode_model(mask, input[start]) ==> start < result)]
pub fn safe_run_end(input: Seq<u8>, start: Int, mask: Seq<u32>) -> Int {
    pearlite! {
        if start >= input.len() || should_encode_model(mask, input[start]) {
            start
        } else {
            safe_run_end(input, start + 1, mask)
        }
    }
}

/// Uniqueness bridge from the scan loop's safety and stop conditions to the
/// logical maximal-run endpoint.
#[cfg(creusot)]
#[logic(opaque)]
#[requires(input.len() > 0 && mask.len() == 4)]
#[requires(0 <= end && end <= input.len())]
#[requires(pearlite! { forall<i: Int> 0 <= i && i < end
    ==> !should_encode_model(mask, input[i]) })]
#[requires(end == input.len() || should_encode_model(mask, input[end]))]
#[ensures(result)]
#[ensures(end == safe_run_end(input, 0, mask))]
pub fn safe_run_end_unique(input: Seq<u8>, end: Int, mask: Seq<u32>) -> bool {
    true
}

/// Extend the checked safe-prefix property by one scanned byte.
#[cfg(creusot)]
#[logic(opaque)]
#[requires(mask.len() == 4)]
#[requires(0 <= end && end < input.len())]
#[requires(pearlite! { forall<i: Int> 0 <= i && i < end
    ==> !should_encode_model(mask, input[i]) })]
#[requires(!should_encode_model(mask, input[end]))]
#[ensures(result)]
#[ensures(pearlite! { forall<i: Int> 0 <= i && i < end + 1
    ==> !should_encode_model(mask, input[i]) })]
pub fn safe_prefix_extend(input: Seq<u8>, mask: Seq<u32>, end: Int) -> bool {
    true
}

/// Checked first-step equation for a maximal unchanged run.
#[cfg(creusot)]
#[logic(opaque)]
#[requires(input.len() > 0 && mask.len() == 4)]
#[requires(!should_encode_model(mask, input[0]))]
#[requires(end == safe_run_end(input, 0, mask))]
#[ensures(result)]
#[ensures(encoded_chunks(mask, input) ==
    Seq::singleton(form_model::byte_sequence_as_ints(input.subsequence(0, end)))
        .concat(encoded_chunks(mask, input.subsequence(end, input.len()))))]
pub fn encoded_chunks_first_run(mask: Seq<u32>, input: Seq<u8>, end: Int) -> bool {
    true
}

/// Checked first-step equation for a selected byte and its `%HH` chunk.
#[cfg(creusot)]
#[logic(opaque)]
#[requires(input.len() > 0 && mask.len() == 4)]
#[requires(should_encode_model(mask, input[0]))]
#[ensures(result)]
#[ensures(encoded_chunks(mask, input) ==
    Seq::singleton(crate::encoded_byte_model(input[0]@))
        .concat(encoded_chunks(mask, input.subsequence(1, input.len()))))]
pub fn encoded_chunks_first_escaped(mask: Seq<u32>, input: Seq<u8>) -> bool {
    true
}

/// Maximal-run/escaped-byte decomposition of a percent-encoded input.
/// Each inner sequence is one requested formatter chunk; escapes use the
/// crate's `%HH` model, including `%20` for space.
#[cfg(creusot)]
#[logic(open)]
#[variant(input.len())]
#[requires(mask.len() == 4)]
#[ensures(pearlite! {
    if input.len() == 0 {
        result.len() == 0
    } else {
        result.len() > 0
            && (if should_encode_model(mask, input[0]) {
                result[0] == crate::encoded_byte_model(input[0]@)
                    && result.subsequence(1, result.len())
                        == encoded_chunks(mask, input.subsequence(1, input.len()))
            } else {
                let end = safe_run_end(input, 0, mask);
                result[0] == form_model::byte_sequence_as_ints(input.subsequence(0, end))
                    && result.subsequence(1, result.len())
                        == encoded_chunks(mask, input.subsequence(end, input.len()))
            })
    }
})]
pub fn encoded_chunks(mask: Seq<u32>, input: Seq<u8>) -> Seq<Seq<Int>> {
    pearlite! {
        if input.len() == 0 {
            Seq::empty()
        } else if should_encode_model(mask, input[0]) {
            Seq::singleton(crate::encoded_byte_model(input[0]@))
                .concat(encoded_chunks(mask, input.subsequence(1, input.len())))
        } else {
            let end = safe_run_end(input, 0, mask);
            Seq::singleton(form_model::byte_sequence_as_ints(
                input.subsequence(0, end)
            )).concat(encoded_chunks(mask, input.subsequence(end, input.len())))
        }
    }
}
