//! Checked collection helper for `PercentEncode`'s `Into<Cow<str>>` path.

#[cfg(feature = "alloc")]
use alloc::{borrow::Cow, string::String};

#[cfg(creusot)]
use creusot_std::prelude::*;
#[cfg(creusot)]
use crate::encode_models;
#[cfg(creusot)]
use form_model;

use crate::PercentEncode;

/// UTF-8 bytes exposed by the returned `Cow`, rather than Unicode scalar
/// values. The encoder's public output contract is byte-oriented.
#[cfg(creusot)]
#[logic(open)]
pub(crate) fn cow_string_bytes(value: Cow<'_, str>) -> Seq<Int> {
    pearlite! {
        match value {
            Cow::Borrowed(s) => form_model::byte_sequence_as_ints(s@.to_bytes()),
            Cow::Owned(s) => form_model::byte_sequence_as_ints(s@.to_bytes()),
        }
    }
}

// Standard-library boundary model: String starts empty and push_str appends
// the borrowed string's scalar sequence. The implementation of alloc::String
// is outside this crate's proof boundary.
#[cfg(creusot)]
extern_spec! {
    impl alloc::string::String {
        #[ensures(result@ == Seq::<char>::empty())]
        fn new() -> String;
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(creusot, ensures((^output)@ == output@.concat(chunk@)))]
#[cfg_attr(creusot, ensures(
    form_model::byte_sequence_as_ints((^output)@.to_bytes())
        == form_model::byte_sequence_as_ints(output@.to_bytes())
            .concat(form_model::string_chunk_bytes(chunk))
))]
fn append_string(output: &mut String, chunk: &str) {
    #[cfg(creusot)]
    proof_assert!(crate::string_bytes_lemmas::string_bytes_concat(output@, chunk@));
    output.push_str(chunk);
}

/// Concatenate chunk bytes as an integer sequence.
#[cfg(creusot)]
#[logic(opaque)]
#[variant(chunks.len())]
#[ensures(pearlite! {
    if chunks.len() == 0 {
        result.len() == 0
    } else {
        result == chunks[0].concat(flatten_chunks(chunks.subsequence(1, chunks.len())))
    }
})]
pub fn flatten_chunks(chunks: Seq<Seq<Int>>) -> Seq<Int> {
    pearlite! {
        if chunks.len() == 0 {
            Seq::empty()
        } else {
            chunks[0].concat(flatten_chunks(chunks.subsequence(1, chunks.len())))
        }
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(creusot, ensures(
    cow_string_bytes(result)
        == flatten_chunks(encode_models::encoded_chunks(
            iter.configured_set(), iter.remaining_input()))
))]
#[cfg_attr(creusot, ensures(
    match result {
        Cow::Borrowed(_) => encode_models::encoded_chunks(
            iter.configured_set(), iter.remaining_input()).len() <= 1,
        Cow::Owned(_) => encode_models::encoded_chunks(
            iter.configured_set(), iter.remaining_input()).len() >= 2,
    }
))]
pub(crate) fn into_cow<'a>(iter: PercentEncode<'a>) -> Cow<'a, str> {
    #[cfg(creusot)]
    let initial = iter.clone();
    let mut iter = iter;
    match iter.next() {
        None => Cow::Borrowed(unsafe { core::str::from_utf8_unchecked(&[]) }),
        Some(first) => match iter.next() {
            None => Cow::Borrowed(first),
            Some(second) => {
                let mut output = String::new();
                #[cfg(creusot)]
                proof_assert!(crate::string_bytes_lemmas::empty_prefix_to_bytes(output@));
                #[cfg(creusot)]
                proof_assert!(form_model::byte_sequence_as_ints(output@.to_bytes())
                    .ext_eq(Seq::empty()));
                append_string(&mut output, first);
                append_string(&mut output, second);
                #[cfg(creusot)]
                let mut visited = ghost!(Seq::<&'a str>::new().into_inner());
                #[cfg(creusot)]
                ghost! {
                    visited.push_back_ghost(first);
                    visited.push_back_ghost(second);
                };
                #[cfg(creusot)]
                proof_assert!((*visited).ext_eq(
                    Seq::singleton(first).concat(Seq::singleton(second)),
                ));
                #[cfg(creusot)]
                proof_assert!(*visited
                    == Seq::singleton(first).concat(Seq::singleton(second)));
                #[cfg(creusot)]
                proof_assert!(Seq::singleton(first).push_back(second)
                    == Seq::singleton(first).concat(Seq::singleton(second)));
                #[cfg(creusot)]
                proof_assert!(encoder_chunks_bytes(Seq::singleton(first))
                    == form_model::string_chunk_bytes(first));
                #[cfg(creusot)]
                proof_assert!(append_encoder_chunk(Seq::singleton(first), second));
                #[cfg(creusot)]
                proof_assert!(initial.produces(
                    Seq::singleton(first).concat(Seq::singleton(second)), iter,
                ));
                #[cfg(creusot)]
                proof_assert!(crate::string_bytes_lemmas::string_bytes_concat(first@, second@));
                #[cfg(creusot)]
                proof_assert!(form_model::byte_sequence_as_ints(output@.to_bytes())
                    == encoder_chunks_bytes(*visited));
                #[cfg(creusot)]
                proof_assert!(initial.configured_set() == iter.configured_set());
                #[cfg(creusot)]
                proof_assert!(encode_models::encoded_chunks(
                    initial.configured_set(), initial.remaining_input(),
                ).len() >= 2);
                #[cfg_attr(creusot, variant(iter.remaining_input().len()))]
                #[cfg_attr(creusot, invariant(initial.produces(*visited, iter)))]
                #[cfg_attr(creusot, invariant(initial.configured_set() == iter.configured_set()))]
                #[cfg_attr(creusot, invariant(form_model::byte_sequence_as_ints(output@.to_bytes())
                    == encoder_chunks_bytes(*visited)))]
                loop {
                    #[cfg(creusot)]
                    let before = snapshot!(iter);
                    match iter.next() {
                        None => break,
                        Some(chunk) => {
                            #[cfg(creusot)]
                            let prefix = snapshot!(*visited);
                            #[cfg(creusot)]
                            let after = snapshot!(iter);
                            append_string(&mut output, chunk);
                            #[cfg(creusot)]
                            {
                                proof_assert!(crate::encoder_display::produces_append(
                                    initial, *prefix, *before, chunk, *after,
                                ));
                                proof_assert!(append_encoder_chunk(*visited, chunk));
                                ghost! { visited.push_back_ghost(chunk); };
                            }
                        }
                    }
                }
                #[cfg(creusot)]
                proof_assert!(encoder_chunks_flatten(*visited));
                #[cfg(creusot)]
                proof_assert!(produces_complete(initial, *visited, iter));
                #[cfg(creusot)]
                proof_assert!(encoder_chunks_bytes(*visited)
                    == flatten_chunks(encode_models::encoded_chunks(
                        initial.configured_set(), initial.remaining_input(),
                    )));
                Cow::Owned(output)
            }
        },
    }
}

#[cfg(creusot)]
#[logic(open)]
fn encoder_chunks_bytes(chunks: Seq<&str>) -> Seq<Int> {
    pearlite! {
        chunks.flat_map(|chunk: &str| form_model::string_chunk_bytes(chunk))
    }
}

#[cfg(creusot)]
#[logic(opaque)]
#[requires(initial.produces(visited, iter))]
#[requires(initial.configured_set() == iter.configured_set())]
#[requires(iter.remaining_input().len() == 0)]
#[ensures(result)]
#[ensures(encode_models::encoded_chunks(
    initial.configured_set(), initial.remaining_input(),
) == visited.map(|chunk: &str| form_model::string_chunk_bytes(chunk)))]
fn produces_complete<'a>(
    initial: PercentEncode<'a>,
    visited: Seq<&'a str>,
    iter: PercentEncode<'a>,
) -> bool {
    encode_models::encoded_chunks(iter.configured_set(), iter.remaining_input()).concat_empty();
    form_model::string_chunk_map_concat(visited, Seq::empty());
    true
}

#[cfg(creusot)]
#[logic(opaque)]
#[variant(chunks.len())]
#[ensures(result)]
#[ensures(encoder_chunks_bytes(chunks)
    == flatten_chunks(chunks.map(|chunk: &str| form_model::string_chunk_bytes(chunk))))]
fn encoder_chunks_flatten(chunks: Seq<&str>) -> bool {
    pearlite! {
        if chunks.len() == 0 {
            encoder_chunks_bytes(chunks)
                == flatten_chunks(chunks.map(|chunk: &str| form_model::string_chunk_bytes(chunk)))
        } else {
            let tail = chunks.tail();
            let mapped = chunks.map(|chunk: &str| form_model::string_chunk_bytes(chunk));
            encoder_chunks_flatten(tail)
                && mapped.subsequence(1, mapped.len()).ext_eq(
                    tail.map(|chunk: &str| form_model::string_chunk_bytes(chunk)))
                && encoder_chunks_bytes(chunks)
                    == flatten_chunks(mapped)
        }
    }
}

#[cfg(creusot)]
#[logic(opaque)]
#[ensures(result)]
#[ensures(encoder_chunks_bytes(chunks.push_back(chunk))
    == encoder_chunks_bytes(chunks).concat(form_model::string_chunk_bytes(chunk)))]
fn append_encoder_chunk(chunks: Seq<&str>, chunk: &str) -> bool {
    chunks.flat_map_push_back::<Int>(chunk, |item: &str| form_model::string_chunk_bytes(item));
    true
}

