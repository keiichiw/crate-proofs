#![no_std]

#[cfg(creusot)]
use creusot_std::prelude::*;
#[cfg(creusot)]
use form_model;

// Isolated bridge corresponding to the production model in crate/src/lib.rs.
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

#[cfg_attr(creusot, requires(mask@.len() == 4))]
#[cfg(creusot)]
pub fn probe_safe_run(input: &[u8], mask: &[u32]) {
    proof_assert!(encode_models::safe_run_end(input@, 0, mask@) <= input@.len());
}

#[cfg_attr(creusot, requires(input@.len() > 0 && mask@.len() == 4))]
#[cfg_attr(creusot, requires(end@ >= 0 && end@ <= input@.len()))]
#[cfg_attr(creusot, requires(pearlite! { forall<i: Int> 0 <= i && i < end@
    ==> !encode_models::should_encode_model(mask@, input@[i]) }))]
#[cfg_attr(creusot, requires(end@ == input@.len()
    || encode_models::should_encode_model(mask@, input@[end@])))]
#[cfg(creusot)]
pub fn probe_run_unique(input: &[u8], mask: &[u32], end: usize) {
    proof_assert!(encode_models::safe_run_end_unique(input@, end@, mask@));
}

#[cfg_attr(creusot, requires(input@.len() > 0 && mask@.len() == 4))]
#[cfg_attr(creusot, requires(!encode_models::should_encode_model(mask@, input@[0])))]
#[cfg(creusot)]
pub fn probe_first_run(input: &[u8], mask: &[u32]) {
    proof_assert!(encode_models::encoded_chunks_first_run(
        mask@, input@, encode_models::safe_run_end(input@, 0, mask@)
    ));
}

#[cfg_attr(creusot, requires(input@.len() > 0 && mask@.len() == 4))]
#[cfg_attr(creusot, requires(encode_models::should_encode_model(mask@, input@[0])))]
#[cfg(creusot)]
pub fn probe_first_escape(input: &[u8], mask: &[u32]) {
    proof_assert!(encode_models::encoded_chunks_first_escaped(mask@, input@));
}

