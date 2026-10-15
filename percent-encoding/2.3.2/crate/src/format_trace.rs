//! Ghost-only observations for checked `PercentEncode` formatting proofs.
//!
//! The trace records each requested `Formatter::write_str` chunk and its
//! returned status. It says nothing about bytes retained by the formatter's
//! underlying writer.

use core::fmt::{self, Formatter};

#[cfg(creusot)]
use creusot_std::prelude::*;
#[cfg(creusot)]
use form_model;

#[cfg(creusot)]
pub(crate) type RequestTrace<'a> = Seq<(&'a str, bool)>;

#[cfg(creusot)]
#[logic(open)]
pub(crate) fn successful_prefix<'a>(
    chunks: Seq<&'a str>,
    trace: RequestTrace<'a>,
    count: Int,
) -> bool {
    pearlite! {
        0 <= count && count <= chunks.len()
            && trace.len() == count
            && forall<j: Int> 0 <= j && j < count ==>
                trace[j].0 == chunks[j] && trace[j].1
    }
}

#[cfg(creusot)]
#[logic(open)]
pub(crate) fn failed_prefix<'a>(chunks: Seq<&'a str>, trace: RequestTrace<'a>, count: Int) -> bool {
    pearlite! {
        0 <= count && count < chunks.len()
            && trace.len() == count + 1
            && (forall<j: Int> 0 <= j && j < count ==>
                trace[j].0 == chunks[j] && trace[j].1)
            && trace[count].0 == chunks[count] && !trace[count].1
    }
}

/// Successful requested writes match the corresponding percent-encoded byte
/// chunks and preserve order. This observes Formatter call requests only.
#[cfg(creusot)]
#[logic(open)]
pub(crate) fn successful_model_prefix<'a>(
    expected: Seq<Seq<Int>>,
    trace: RequestTrace<'a>,
    count: Int,
) -> bool {
    pearlite! {
        0 <= count && count <= expected.len()
            && trace.len() == count
            && forall<j: Int> 0 <= j && j < count ==>
                form_model::string_chunk_bytes(trace[j].0) == expected[j]
                    && trace[j].1
    }
}

/// Successful requests followed by the first failed requested write, matched
/// to the encoded byte chunks. No underlying sink contents are observed.
#[cfg(creusot)]
#[logic(open)]
pub(crate) fn failed_model_prefix<'a>(
    expected: Seq<Seq<Int>>,
    trace: RequestTrace<'a>,
    count: Int,
) -> bool {
    pearlite! {
        0 <= count && count < expected.len()
            && trace.len() == count + 1
            && (forall<j: Int> 0 <= j && j < count ==>
                form_model::string_chunk_bytes(trace[j].0) == expected[j]
                    && trace[j].1)
            && form_model::string_chunk_bytes(trace[count].0) == expected[count]
            && !trace[count].1
    }
}

/// Append a successful request to a checked model prefix.
#[cfg(creusot)]
#[logic(opaque)]
#[requires(successful_model_prefix(expected, trace, count))]
#[requires(count < expected.len())]
#[requires(form_model::string_chunk_bytes(chunk) == expected[count])]
#[ensures(result)]
#[ensures(successful_model_prefix(
    expected, trace.push_back((chunk, true)), count + 1,
))]
pub(crate) fn successful_model_prefix_push<'a>(
    expected: Seq<Seq<Int>>,
    trace: RequestTrace<'a>,
    count: Int,
    chunk: &'a str,
) -> bool {
    true
}

/// Append the first failed request to the preceding successful model prefix.
#[cfg(creusot)]
#[logic(opaque)]
#[requires(successful_model_prefix(expected, trace, count))]
#[requires(count < expected.len())]
#[requires(form_model::string_chunk_bytes(chunk) == expected[count])]
#[ensures(result)]
#[ensures(failed_model_prefix(
    expected, trace.push_back((chunk, false)), count,
))]
pub(crate) fn failed_model_prefix_push<'a>(
    expected: Seq<Seq<Int>>,
    trace: RequestTrace<'a>,
    count: Int,
    chunk: &'a str,
) -> bool {
    true
}

/// Make one formatter write and record the exact request and returned status.
/// The ghost argument and update erase completely from native builds.
#[cfg_attr(
    creusot,
    ensures((^*trace) == (**trace).push_back((chunk, match result {
        Ok(()) => true,
        Err(_) => false,
    })))
)]
pub(crate) fn request_write<'a: 'b, 'b>(
    formatter: &mut Formatter<'_>,
    chunk: &'a str,
    #[cfg(creusot)] mut trace: Ghost<&'b mut RequestTrace<'a>>,
) -> fmt::Result {
    let result = formatter.write_str(chunk);

    #[cfg(creusot)]
    {
        let succeeded = match &result {
            Ok(()) => true,
            Err(_) => false,
        };
        ghost! {
            let event = (chunk, succeeded);
            (**trace).push_back_ghost(event);
        };
    }

    result
}
