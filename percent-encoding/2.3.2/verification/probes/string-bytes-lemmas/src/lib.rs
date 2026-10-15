#![no_std]

#[cfg(creusot)]
use creusot_std::prelude::*;
#[cfg(creusot)]
use form_model;

#[path = "../../../../crate/src/string_bytes_lemmas.rs"]
#[allow(dead_code)]
mod string_bytes_lemmas;

#[cfg(creusot)]
pub fn probe_string_bytes_concat(prefix: &str, suffix: &str) {
    proof_assert!(string_bytes_lemmas::string_bytes_concat(prefix@, suffix@));
    proof_assert!(prefix@.concat(suffix@).to_bytes()
        == prefix@.to_bytes().concat(suffix@.to_bytes()));
    proof_assert!(form_model::byte_sequence_as_ints(prefix@.concat(suffix@).to_bytes())
        == form_model::byte_sequence_as_ints(prefix@.to_bytes())
            .concat(form_model::byte_sequence_as_ints(suffix@.to_bytes())));
}
