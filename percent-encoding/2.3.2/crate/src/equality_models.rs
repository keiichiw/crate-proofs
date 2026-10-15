//! Logical equality models for percent-encoding values.
//!
//! Equality for an encoder is equality of its remaining source bytes and its
//! configured ASCII set. This deliberately models the iterator state, rather
//! than the rendered encoding, which can depend on how much input has already
//! been consumed.

#[cfg(creusot)]
use creusot_std::prelude::*;

/// Exact equality of the observable state of two percent encoders.
#[cfg(creusot)]
#[logic(open)]
pub fn percent_encode_eq_model(
    left_input: Seq<u8>,
    left_set: Seq<u32>,
    right_input: Seq<u8>,
    right_set: Seq<u32>,
) -> bool {
    pearlite! { left_input == right_input && left_set == right_set }
}

/// Recover equality of byte-slice views from equality of their integer models.
/// Slice DeepModel maps each byte to its integer view; this explicit bridge
/// supplies the sequence extensionality needed by encoder equality.
#[cfg(creusot)]
#[logic(opaque)]
#[requires(left.deep_model() == right.deep_model())]
#[ensures(result)]
#[ensures(left@.ext_eq(right@))]
pub(crate) fn slice_byte_views_ext_eq_from_model(left: &[u8], right: &[u8]) -> bool {
    let left_model = left.deep_model();
    let right_model = right.deep_model();
    proof_assert!(left@.len() == left_model.len());
    proof_assert!(right@.len() == right_model.len());
    proof_assert!(left@.len() == right@.len());
    proof_assert!(pearlite! {
        forall<i: Int> 0 <= i && i < left@.len()
            ==> left@[i]@ == right@[i]@
    });
    proof_assert!(left@.ext_eq(right@));
    true
}
