//! Checked concatenation lemmas for UTF-8 byte views of character sequences.

#[cfg(creusot)]
use creusot_std::prelude::*;
#[cfg(creusot)]
use form_model;

#[cfg(creusot)]
#[logic(opaque)]
#[requires(left.len() > 0)]
#[requires(0 <= i && i < left.tail().concat(right).len())]
#[ensures(result)]
#[ensures(left.concat(right).tail()[i] == left.tail().concat(right)[i])]
fn nonempty_tail_at_index<T>(left: Seq<T>, right: Seq<T>, i: Int) -> bool {
    let joined = left.concat(right);
    let joined_tail = joined.tail();
    let tail_left = left.tail();
    let tail_joined = tail_left.concat(right);
    let boundary = left.len() - 1;
    proof_assert!(joined_tail.len() == tail_joined.len());
    proof_assert!(tail_left.len() == boundary);
    if i < boundary {
        proof_assert!(i < joined_tail.len());
        proof_assert!(i + 1 < left.len());
        proof_assert!(i + 1 < joined.len());
        proof_assert!(joined_tail[i] == joined[i + 1]);
        proof_assert!(joined[i + 1] == left[i + 1]);
        proof_assert!(tail_joined[i] == tail_left[i]);
        proof_assert!(tail_left[i] == left[i + 1]);
        proof_assert!(joined_tail[i] == tail_joined[i]);
    } else {
        proof_assert!(0 <= i - boundary && i - boundary < right.len());
        proof_assert!(0 <= i + 1 - left.len() && i + 1 - left.len() < right.len());
        proof_assert!(i + 1 < joined.len());
        proof_assert!(joined_tail[i] == joined[i + 1]);
        proof_assert!(joined[i + 1] == right[i + 1 - left.len()]);
        proof_assert!(tail_joined[i] == right[i - tail_left.len()]);
        proof_assert!(right[i + 1 - left.len()] == right[i - tail_left.len()]);
        proof_assert!(joined_tail[i] == tail_joined[i]);
    }
    true
}

#[cfg(creusot)]
#[logic(opaque)]
#[requires(left.len() > 0)]
#[ensures(result)]
#[ensures(left.concat(right).tail().ext_eq(left.tail().concat(right)))]
fn nonempty_left_concat_tail<T>(left: Seq<T>, right: Seq<T>) -> bool {
    let joined_tail = left.concat(right).tail();
    let tail_joined = left.tail().concat(right);
    proof_assert!(joined_tail.len() == tail_joined.len());
    proof_assert!(pearlite! {
        forall<i: Int> 0 <= i && i < joined_tail.len()
            ==> nonempty_tail_at_index(left, right, i)
    });
    proof_assert!(joined_tail.ext_eq(tail_joined));
    true
}

#[cfg(creusot)]
#[logic(opaque)]
#[requires(prefix.len() == 0)]
#[ensures(result)]
#[ensures(prefix.ext_eq(Seq::empty()))]
#[ensures(prefix.to_bytes().ext_eq(Seq::empty()))]
pub(crate) fn empty_prefix_to_bytes(prefix: Seq<char>) -> bool {
    proof_assert!(prefix.ext_eq(Seq::empty()));
    proof_assert!(prefix.to_bytes().ext_eq(Seq::empty()));
    true
}

#[cfg(creusot)]
#[logic(opaque)]
#[requires(prefix.len() == 0)]
#[ensures(result)]
#[ensures(prefix.concat(suffix).to_bytes()
    == prefix.to_bytes().concat(suffix.to_bytes()))]
fn empty_string_bytes_concat(prefix: Seq<char>, suffix: Seq<char>) -> bool {
    suffix.concat_empty();
    pearlite! {
        empty_prefix_to_bytes(prefix)
            && byte_sequence_as_ints_concat(prefix.to_bytes(), suffix.to_bytes())
            && prefix.concat(suffix).to_bytes()
                == prefix.to_bytes().concat(suffix.to_bytes())
    }
}

#[cfg(creusot)]
#[logic(opaque)]
#[variant(left.len())]
#[ensures(result)]
#[ensures(form_model::byte_sequence_as_ints(left.concat(right))
    == form_model::byte_sequence_as_ints(left)
        .concat(form_model::byte_sequence_as_ints(right)))]
fn byte_sequence_as_ints_concat(left: Seq<u8>, right: Seq<u8>) -> bool {
    pearlite! {
        if left.len() == 0 {
            true
        } else {
            nonempty_left_concat_tail(left, right)
                && byte_sequence_as_ints_concat(left.tail(), right)
        }
    }
}

/// Prove that UTF-8 byte conversion distributes over character concatenation,
/// both as raw bytes and through the dependency's byte-to-integer model.
#[cfg(creusot)]
#[logic(opaque)]
#[variant(prefix.len())]
#[ensures(result)]
#[ensures(prefix.concat(suffix).to_bytes()
    == prefix.to_bytes().concat(suffix.to_bytes()))]
#[ensures(form_model::byte_sequence_as_ints(prefix.concat(suffix).to_bytes())
    == form_model::byte_sequence_as_ints(prefix.to_bytes())
        .concat(form_model::byte_sequence_as_ints(suffix.to_bytes())))]
pub(crate) fn string_bytes_concat(prefix: Seq<char>, suffix: Seq<char>) -> bool {
    pearlite! {
        if prefix.len() == 0 {
            empty_string_bytes_concat(prefix, suffix)
                && byte_sequence_as_ints_concat(prefix.to_bytes(), suffix.to_bytes())
        } else {
            let joined = prefix.concat(suffix);
            let tail = prefix.tail();
            nonempty_left_concat_tail(prefix, suffix)
                && string_bytes_concat(tail, suffix)
                && byte_sequence_as_ints_concat(prefix.to_bytes(), suffix.to_bytes())
                && joined.to_bytes()
                    == prefix.to_bytes().concat(suffix.to_bytes())
        }
    }
}
