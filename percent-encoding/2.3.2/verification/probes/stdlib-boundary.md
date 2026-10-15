# UTF-8 standard-library boundary ledger

These models are explicit assumptions about Rust standard-library behavior.
Creusot proves that the wrapper bodies preserve the models; it does not prove
the standard-library implementation.

| Boundary | Modeled property | Open behavior |
| --- | --- | --- |
| `String::from_utf8_lossy` | Inherited model: exact lossy scalar output; borrowed result iff bytes are valid UTF-8; borrowed byte content is unchanged. | Rust implementation and allocation behavior. |
| `str::from_utf8` | New module model: `Ok` iff a scalar sequence encodes to the exact input bytes; successful `str` content equals that sequence. `Err` iff no such sequence exists. On `Err`, `valid_up_to` and `error_len` match a locally defined recursive UTF-8 recognizer. | Rust implementation and adequacy of the assumed standard contract relative to the recognizer. The recognizer is not proved equivalent to the separate existential `Seq<char>::to_bytes` validity model. |
| `String::from_utf8` | Strict probe only: exact successful scalar content; `Err` iff input is invalid UTF-8. | Error byte preservation and implementation. |
| `FromUtf8Error::utf8_error` | Strict probe only: typed error result; no field-level model. | Exact error offset/length and correspondence to `str::from_utf8` errors. |
| `String::from_utf8_unchecked` | Reuses the inherited precondition requiring a scalar sequence whose UTF-8 bytes equal the vector; successful result preserves that string view. | Rust implementation and memory safety of the standard library API itself. |

`utf8_models::decode_utf8` does not call `String::from_utf8` or
`FromUtf8Error::utf8_error`: it validates owned bytes with `str::from_utf8`,
returns that exact error on failure, and converts the already validated owned
vector with the inherited `String::from_utf8_unchecked` contract on success.
This is intended to perform one validation pass and move the existing vector
without a new allocation, matching the `String::from_utf8` path. The strict
wrapper contract covers valid content, invalid-error classification, exact
error details as modeled at the standard-library boundary, and borrowed/owned
policy. The `utf8_step`/`strict_error` logic is local and contains no trusted
lemma; the extern contract assumes standard-library errors agree with that
recognizer. Native differential checks compare the error fields on their finite
corpus, but do not prove standard-library correctness.

The strict API probe separately translates and proves a wrapper that calls
all three strict APIs. Its `FromUtf8Error::utf8_error` postcondition is
deliberately vacuous: the wrapper only promises an error for invalid bytes,
not the observable error fields. The strict probe is feasibility evidence for
those stated contracts, not production API proof.

The lossy helper's owned-valid path has a debug-only runtime assertion change:
pointer identity was replaced with byte-content equality. This incurs an
additional linear comparison only in debug builds; release builds compile out
the assertion. The change does not alter release output, allocation, or
pointer-related API guarantees. The phase 2 native differential run predates
this helper integration, so an updated finite differential check is still
required before claiming observed correspondence for this runtime change.
