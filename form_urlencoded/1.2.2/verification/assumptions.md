# Model and exclusion ledger

The historical byte-core milestone used no application-level `trusted` declarations or custom axioms. Later source changes invalidate its input fingerprint for current-code claims; its archived ledger and manifest are retained for historical review.

Current selected functions use Creusot 0.13 and `creusot-std` 0.13 models for integer arithmetic, `u8`, slices, and mutable slices. Review current source contracts and fresh evidence together. No application algorithm or percent-decoding/encoding algorithm is trusted.

`crate/src/stdlib_models.rs` defines the UTF-8 recognizer and maximal-subpart lossy decoder as checked logic over the canonical `Seq<Int>` byte trace. Its standard-library extern contracts are:

- `String::from_utf8_lossy` returns the exact modeled scalar sequence for every byte input, returns `Cow::Borrowed` exactly for valid UTF-8 and `Cow::Owned` otherwise, and the borrowed string encodes to the identical input bytes. Standard `&[u8]` values are mapped to integer bytes before calling the model.
- `str::as_bytes` exposes exactly the string's UTF-8 byte sequence. This is a content contract; it does not establish pointer identity or provenance.
- `core::str::from_utf8_unchecked` preserves the byte sequence and requires either an all-ASCII input or an explicit scalar sequence whose UTF-8 encoding equals the bytes. This is a sound subset of the standard unsafe method's valid-UTF-8 precondition, not a complete recognizer for all valid byte input.
- Slice `split_first` and `split_at` return exact elements and subsequences.
- The existing `Vec<T>` `Deref` model returns a slice whose sequence equals the vector's sequence; the decoder can use that standard-library boundary without a new extern assumption.
- `String::push_str` appends the suffix's scalar sequence. `String::truncate` is a no-op when the requested byte length is at least the current length; below that, its normal-return contract requires a character boundary and returns that prefix. A shorter non-boundary offset is outside the contract domain and panics in the standard method.

The model design, including exclusions and the isolated translation probe, is in [`stdlib-model-design.md`](stdlib-model-design.md). The probe checks translation only. Its ad hoc SMT attempt for slice copying was blocked by a local Why3 socket permission error and does not count as proof evidence. No fresh proof closure of the standard-library implementation is claimed.

Other relevant behavior comes from existing `creusot-std` 0.13 contracts: `String::from_utf8_unchecked(Vec<u8>)` requires a scalar-sequence UTF-8 witness and preserves bytes; `ToOwned for str` preserves string content; `u8::clone` is modeled as identity; and slice `to_vec` preserves length and each element's `Clone` postcondition. For `u8`, these contracts compose to the exact byte-vector view used by the local copy helper. They are standard-library model boundaries, not application `trusted` declarations. There is no blanket `Cow::into_owned` content assumption: the inherent method is generic over caller-implementable `ToOwned`; the UTF-8 wrapper handles borrowed and owned cases explicitly and relies on the concrete `str` model where applicable.

The local percent decoder is application code and remains checked; `percent-encoding` 2.3.2 is not assumed to implement it correctly. Parser ownership is specified by checked logic: percent decoding borrows exactly when no valid escape causes a replacement; the complete decode borrows only when plus replacement is absent, percent decoding preserves the input length, and the resulting bytes are valid UTF-8. The parser's separate ownership trace records those results for each returned field.

The exact `EncodingOverride` function-pointer trait object is rejected by Creusot 0.13 (`forbidden dyn type`), so callback output and behavior are not in the selected proof. Generic `Target` guarantees are conditional on the particular target's checked trait contracts; no laws are assumed for arbitrary implementations. Custom iterator bodies and trait refinements remain distinct claims. Run outcomes and current-input freshness are recorded in [results.md](results.md); this ledger defines the assumptions, not the execution status.
