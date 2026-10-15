//! Checked ghost model for replacing form-urlencoded `+` bytes with spaces.

use creusot_std::prelude::*;

/// Pointwise replacement of every plus byte by an ASCII space.
#[logic(open)]
pub fn replace_plus_model(bytes: Seq<u8>) -> Seq<u8> {
    pearlite! { bytes.map(|byte: u8| if byte@ == 43 { 32u8 } else { byte }) }
}

/// Connect a plus-free byte sequence to the identity case of the model.
#[logic(opaque)]
#[requires(forall<i: Int> 0 <= i && i < bytes.len() ==> bytes[i]@ != 43)]
#[ensures(result)]
#[ensures(replace_plus_model(bytes) == bytes)]
pub fn no_plus_identity(bytes: Seq<u8>) -> bool {
    true
}

/// Connect a checked pointwise replacement trace to the map model.
#[logic(opaque)]
#[requires(result_bytes.len() == original.len())]
#[requires(forall<i: Int> 0 <= i && i < original.len() ==>
    result_bytes[i]@ == if original[i]@ == 43 { 32 } else { original[i]@ })]
#[ensures(result)]
#[ensures(result_bytes == replace_plus_model(original))]
pub fn plus_result_exact(original: Seq<u8>, result_bytes: Seq<u8>) -> bool {
    true
}
