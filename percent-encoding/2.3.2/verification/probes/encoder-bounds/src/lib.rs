#![no_std]

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

#[path = "../../../../crate/src/encode_models.rs"]
#[allow(dead_code)]
mod encode_models;

#[path = "../../../../crate/src/encoder_bounds.rs"]
#[allow(dead_code)]
mod encoder_bounds;

#[cfg_attr(creusot, requires(mask@.len() == 4))]
#[cfg(creusot)]
pub fn probe_encoded_chunk_count_bounds(mask: &[u32], input: &[u8]) {
    proof_assert!(encoder_bounds::encoded_chunk_count_bounds(mask@, input@));
    proof_assert!(
        encode_models::encoded_chunks(mask@, input@).len() <= input@.len()
    );
    proof_assert!(
        (input@.len() == 0) == (encode_models::encoded_chunks(mask@, input@).len() == 0)
    );
    proof_assert!(
        input@.len() > 0 ==> encode_models::encoded_chunks(mask@, input@).len() >= 1
    );
}
