//! Checked `Display` loop for a percent encoder.
//!
//! The trace records requested `Formatter::write_str` calls and their return
//! statuses. It does not describe the formatter's underlying writer output.

use core::fmt::{self, Formatter};

#[cfg(creusot)]
use creusot_std::prelude::*;
#[cfg(creusot)]
use creusot_std::std::iter::IteratorSpec;
#[cfg(creusot)]
use form_model;

use crate::{format_trace, PercentEncode};

/// Compose one successful iterator step with the chunks visited so far.
#[cfg(creusot)]
#[logic(opaque)]
#[requires(initial.produces(prefix, before))]
#[requires(before.produces(Seq::singleton(chunk), after))]
#[ensures(result)]
#[ensures(initial.produces(prefix.push_back(chunk), after))]
pub(crate) fn produces_append<'a>(
    initial: PercentEncode<'a>,
    prefix: Seq<&'a str>,
    before: PercentEncode<'a>,
    chunk: &'a str,
    after: PercentEncode<'a>,
) -> bool {
    <PercentEncode<'a> as IteratorSpec>::produces_trans(
        initial,
        prefix,
        before,
        Seq::singleton(chunk),
        after,
    );
    proof_assert!(prefix.push_back(chunk).ext_eq(
        prefix.concat(Seq::singleton(chunk)),
    ));
    true
}

/// Relate the next visited string chunk to the encoded model at its position.
#[cfg(creusot)]
#[logic(opaque)]
#[requires(expected == crate::encode_models::encoded_chunks(
    initial.configured_set(), initial.remaining_input(),
))]
#[requires(initial.produces(prefix.push_back(chunk), after))]
#[ensures(result)]
#[ensures(prefix.len() < expected.len())]
#[ensures(form_model::string_chunk_bytes(chunk) == expected[prefix.len()])]
fn produced_chunk_matches<'a>(
    expected: Seq<Seq<Int>>,
    initial: PercentEncode<'a>,
    prefix: Seq<&'a str>,
    chunk: &'a str,
    after: PercentEncode<'a>,
) -> bool {
    form_model::string_chunk_map_concat(prefix, Seq::singleton(chunk));
    form_model::string_chunk_singleton(chunk);
    true
}

/// Format all chunks produced by `encoder`, stopping and returning the first
/// formatter error unchanged.
pub(crate) fn format_encoder(
    encoder: &PercentEncode<'_>,
    formatter: &mut Formatter<'_>,
) -> fmt::Result {
    let mut iter = encoder.clone();
    #[cfg(creusot)]
    let expected = snapshot!(crate::encode_models::encoded_chunks(
        encoder.configured_set(),
        encoder.remaining_input(),
    ));
    #[cfg(creusot)]
    let mut visited = Seq::new();
    #[cfg(creusot)]
    let mut trace = Seq::new();

    #[cfg(creusot)]
    let initial = snapshot!(iter);

    #[cfg_attr(creusot, invariant((*visited).len() == (*trace).len()))]
    #[cfg_attr(creusot, invariant(initial.produces(*visited, iter)))]
    #[cfg_attr(creusot, invariant(format_trace::successful_model_prefix(
        *expected, *trace, (*trace).len(),
    )))]
    #[cfg_attr(creusot, variant(iter.remaining_input().len()))]
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
                #[cfg(creusot)]
                {
                    ghost! {
                        visited.push_back_ghost(chunk);
                    };
                    proof_assert!(produces_append(
                        *initial,
                        *prefix,
                        *before,
                        chunk,
                        *after,
                    ));
                }

                #[cfg(creusot)]
                let trace_before = snapshot!(*trace);
                let result = format_trace::request_write(
                    formatter,
                    chunk,
                    #[cfg(creusot)] trace.borrow_mut(),
                );
                match result {
                    Err(error) => {
                        #[cfg(creusot)]
                        {
                            proof_assert!(produced_chunk_matches(
                                *expected, *initial, *prefix, chunk, *after,
                            ));
                            proof_assert!(format_trace::failed_model_prefix_push(
                                *expected, *trace_before, (*trace_before).len(), chunk,
                            ));
                        }
                        return Err(error);
                    }
                    Ok(()) => {
                        #[cfg(creusot)]
                        {
                            proof_assert!(produced_chunk_matches(
                                *expected, *initial, *prefix, chunk, *after,
                            ));
                            proof_assert!(format_trace::successful_model_prefix_push(
                                *expected, *trace_before, (*trace_before).len(), chunk,
                            ));
                        }
                    }
                }
            }
        }
    }

    #[cfg(creusot)]
    {
        proof_assert!(format_trace::successful_model_prefix(
            *expected, *trace, (*trace).len(),
        ));
        proof_assert!((*visited).len() == (*expected).len());
    }
    Ok(())
}
