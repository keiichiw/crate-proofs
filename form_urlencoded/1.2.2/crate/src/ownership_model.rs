//! Pure ownership predicates for the byte-decoding fast path.

use alloc::borrow::Cow;
use creusot_std::prelude::*;

#[logic(open)]
pub fn no_plus(bytes: Seq<u8>) -> bool {
    pearlite! { forall<i: Int> 0 <= i && i < bytes.len() ==> bytes[i]@ != 43 }
}

#[logic(open)]
pub fn cow_bytes_borrowed(value: Cow<'_, [u8]>) -> bool {
    match value {
        Cow::Borrowed(_) => true,
        Cow::Owned(_) => false,
    }
}

#[logic(open)]
pub fn cow_str_borrowed(value: Cow<'_, str>) -> bool {
    match value {
        Cow::Borrowed(_) => true,
        Cow::Owned(_) => false,
    }
}

#[logic(open)]
pub fn decode_borrows(bytes: Seq<u8>) -> bool {
    no_plus(bytes)
        && {
            let decoded = crate::percent_decoded_model(
                crate::byte_sequence_as_ints(crate::plus_model::replace_plus_model(bytes)),
            );
            decoded.len() == bytes.len() && crate::stdlib_models::utf8_is_valid(decoded)
        }
}
