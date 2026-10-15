# Standard-library model supplement: UTF-8 lossy conversion

`crate/src/stdlib_models.rs` isolates the standard-library boundary used by
`decode_utf8_lossy`. Its `utf8_step` definition is checked ghost code over the
canonical `Seq<Int>` byte trace and returns
`(Unicode scalar value, consumed byte count, validity)`. Standard slice inputs
are mapped from `u8` with `bytes@.map(|b: u8| b@)`. The logic is totalized for
integers outside the byte range by treating each as an invalid one-unit input;
standard-library calls only supply mapped `u8` values in `0..=255`.
`utf8_lossy_model` recursively emits that scalar or U+FFFD (65533), and
`utf8_is_valid` recursively requires every step to be valid. Scalar values use
`Seq<Int>` so the model does not need an assumed Int-to-char constructor.

The step rules distinguish canonical 2-, 3-, and 4-byte UTF-8 encodings,
including the E0/ED/F0/F4 second-byte restrictions that reject overlong forms,
surrogates, and values above U+10FFFF. An invalid lead consumes one byte. A
bad continuation consumes only its preceding valid prefix, leaving the offending
byte for the next step. A truncated, otherwise-valid prefix at end of input is
replaced as one subpart consuming the remaining bytes. These are the maximal
subparts used by Rust's `String::from_utf8_lossy`.

The standard-library boundary in this file specifies `String::from_utf8_lossy`
against the explicit model for every byte sequence; it returns
`Cow::Borrowed` exactly for valid UTF-8 and `Cow::Owned` otherwise, and a
borrowed string encodes to the identical input bytes. This is the principal
assumed API behavior and covers the documented semantics on the selected Rust
target. The file also gives content contracts to `str::as_bytes`,
`str::from_utf8_unchecked`, slice `split_first`/`split_at`, and String
`push_str`/`truncate`, where each call is used by the selected
implementation. A vector-to-slice borrow uses the existing `Vec<T>` `Deref`
model, which preserves the vector's sequence; no new `as_slice` extern model
is added.
The unchecked conversion accepts either an all-ASCII byte sequence or an
explicit UTF-8 scalar-sequence witness. This is a sound documented subset of
its valid-UTF-8 safety domain, including the byte serializer's ASCII path; it
does not claim to characterize every valid input. `truncate` is modeled on its
full successful-return domain: a requested byte length at or above the current
length is a no-op, while a shorter length requires a UTF-8 character boundary.
The standard method panics for a shorter non-boundary offset. The existing
Creusot std model already specifies `String::from_utf8_unchecked(Vec<u8>)` with
an equivalent existential witness and byte-preservation postcondition; it is
not duplicated here.

There is deliberately no blanket `Cow::into_owned` postcondition. The inherent
method is generic over caller-implementable `ToOwned`, and a generic model that
unconditionally equates the owned value's content with the borrowed value
would assume an unmodeled trait law. Creusot already specifies `ToOwned for
str`; a focused call-site proof may use that concrete model, but this file does
not make a stronger assumption for other `Cow` types. None of these contracts
verifies the standard-library implementation, allocation behavior, or OOM
behavior.

Pointer provenance is not part of this model. Byte equality of the borrowed
result does not establish that its fat pointer is identical to the input slice
pointer. The wrapper's debug assertion now checks byte-content equality, which
is supported by the lossy-conversion and `as_bytes` content contracts; this
model makes no pointer-identity claim.
Likewise, this model says nothing about `percent_decode`, arbitrary encoding
callbacks, or the application implementation of parsing and decoding.

`verification/probes/stdlib` is an isolated translation probe that imports this
file without changing the crate module graph. Its `copy` function also probes
`&[u8]::to_vec()` against the existing Creusot slice contract and primitive
`u8::clone` model. Translation generates the exact slice-to-Vec view goal; an earlier
isolated SMT attempt was blocked by a local Why3 socket permission error, so no
proof closure is claimed from that probe. This is not product API evidence.
