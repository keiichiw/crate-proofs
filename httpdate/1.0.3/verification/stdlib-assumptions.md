# Conditional standard-library assumptions used by production proofs

`crate/src/stdlib_specs.rs` makes the reviewed boundary models from the
independent [boundary-model trial](trial/boundary-model/README.md) available to
the production proof configuration. Any proof that reaches these contracts is
conditional on the assumptions recorded here. This does not verify the Rust
standard-library implementations.

The proof scope is limited to **64-bit Linux or macOS arm64** and the supported `httpdate`
date domain (`UNIX_EPOCH <= t < 253402300800` seconds after the epoch). The
`SystemTime + Duration` contract is narrower still: its left operand must be
`UNIX_EPOCH`, and the duration must represent a supported date before the
year-10000 boundary. The `duration_since` model applies only when the timestamp
difference fits in `Duration`; it specifies the successful duration and the
sign of the error case, but not the error value. No timestamp monotonicity or
behavior of clock reads is assumed.

The production proof currently relies on **41 conditional standard-library
declarations/models**. The first eleven are the timestamp, ASCII, and formatter
models:

1. `time_ns`: an opaque timestamp in nanoseconds.
2. `UNIX_EPOCH`: model value zero.
3. `SystemTime::duration_since`: for differences within the representable
   `Duration` range, return the nonnegative difference or an error for a
   negative difference; the error value is unconstrained.
4. `SystemTime + Duration`: on 64-bit Linux or macOS arm64, adding a supported duration to
   the epoch yields the summed timestamp.
5. `str::from_utf8`: ASCII bytes convert successfully while preserving
   characters.
6. `str::is_ascii`: recognize strings whose code points are all below 128.
7. `str::trim`: on ASCII strings, remove whitespace bytes 9..13 and 32,
   including vertical tab.
8. `str::as_bytes`: on ASCII strings, preserve byte values.

Formatter adds three trusted declarations:

9. `formatter_output`: an opaque model of the content written through a
   `Formatter`.
10. `append_sink`: an opaque predicate saying whether a formatter's underlying
    writer faithfully appends successful writes.
11. The fully-qualified
    `<Formatter<'_> as std::fmt::Write>::write_str` contract: formatter options
    are preserved, and `append_sink` remains true if it was true before the
    call. On `Ok(())`, if `append_sink` holds on entry, the model output grows
    by the input text. On `Err`, the contract gives no output guarantee. This
    is the trait method used by the application formatter; the inherent
    `Formatter::write_str` has its own standard-library specification and is
    not overridden here. Rust 1.91's inherent and trait methods both forward
    unchanged to the underlying buffer's `write_str`. The pinned source review
    is recorded in [stdlib-reference.json](stdlib-reference.json).

The formatter guarantee is conditional. It does not promise output for an
arbitrary sink whose append behavior is unknown, and it leaves partial writes
on `Err` unconstrained. It also makes no assumption that the formatter starts
with empty output: the postcondition relates the resulting output to its prior
output by appending the text.

### Hash protocol assumptions

Declarations 12–22 support the selected `HttpDate::hash`
contract. They are conditional on the type-level `supported_hasher::<H>()`
predicate, which assumes that `H` has deterministic, total, nonpanicking
`write_u8`, `write_u16`, and `finish` behavior and that its model state records
all internal state needed to predict future calls and the final digest.

12. `supported_hasher::<H>()`: the type-level condition above.
13. `hash_state(&H)`: an opaque integer model of sufficient internal state.
14. `hash_step_u8(state, value)`: the modeled state transition for `u8`.
15. `hash_step_u16(state, value)`: the modeled state transition for `u16`.
16. `hash_finish(state)`: the modeled `u64` result for a completed state.
17. `Hash::hash`: requires a supported hasher type.
18. `Hasher::finish`: requires a supported type and returns its model state's
    `hash_finish` value.
19–20. The standard `Hash` implementations for `u8` and `u16`: each advances
    the model state using the corresponding typed step.
21. `DefaultHasher::new`: returns a supported hasher with model state zero.
    The pinned Rust sources show this constructor initializes `SipHasher13`
    with fixed keys `(0, 0)`.
22. `DefaultHasher::finish`: returns the modeled finish value for its state.

`hash_state` represents sufficient internal state, not the historical sequence
of writes. It need not be injective, and distinct dates may produce the same
state or digest; a deterministic no-op hasher is compatible with the absence of
collision-freedom guarantees. The equality lemma requires the same hasher type
and equal complete initial model states. `DefaultHasher::new` supplies a
concrete supported witness, and two fresh instances begin in the same modeled
state. No fixed digest values, cross-version stability, or behavior for
arbitrary unsupported `Hasher` types is promised. The standard `Hash::hash_slice`
method has no formal contract here; its pinned-source default and native
regression are not part of the production Hash proof guarantee.

### `io::Error` assumptions

Declarations 23–26 support the selected `From<Error> for io::Error`
body and its kind/payload refinement:

23. `io_kind(io::Error)`: an opaque model of the error kind.
24. `io_payload::<E>(io::Error)`: an opaque model of an optional concrete
    payload value.
25. `io::Error::new(kind, error)`, restricted to
    `E: Error + Send + Sync + 'static`: records the supplied kind and the
    supplied concrete payload as `Some(error)`. This is the direct-payload
    constructor contract used by the application; it does not model arbitrary
    `Into<Box<dyn Error>>` conversions.
26. `io::Error::kind`: returns the modeled kind.

These assumptions do not model `get_ref`, dynamic downcasting, or
`into_inner`. Native tests check that the current standard library retains and
exposes the payload through those APIs, but those observations are not
production proof guarantees.

### `Debug` assumptions

The final fifteen declarations support the checked Debug behavior for the
public `HttpDate` and `Error` implementations, under the formatter conditions
below:

27. `debug_options(Formatter)`: an opaque model of flags, width, precision,
    fill, and alignment.
28–32. `Formatter::{flags,width,precision,fill,align}` return the matching
    modeled option.
33–38. `Formatter::{debug_struct,debug_tuple}` and the `field` / `finish`
    methods on `DebugStruct` and `DebugTuple` provide the builder interfaces.
    These declarations give no content postcondition for builder output.
39–41. The standard `Debug` implementations for `u8`, `u16`, and `()`.
    For successful writes to a faithful append sink under `plain_options`,
    the numeric implementations append the exact decimal digits and unit
    appends `()`; they preserve formatter options and the append-sink condition.

`plain_options` means flags are `0` (normal Debug) or `4` (alternate pretty
Debug), width and precision are `None`, fill is a space, and alignment is
`None`. For these options, `Debug for HttpDate` writes `HttpDate` followed by
the seven fields in order: `sec`, `min`, `hour`, `day`, `mon`, `year`, and
`wday`; numeric field values use decimal digits. Normal output uses the
standard one-line field separators. Alternate output uses four-space field
indentation and one field per line. `Debug for Error` appends exactly
`Error(())` in normal mode and `Error(\n    (),\n)` in alternate mode.

The application Debug implementations check `debug_mode` and use explicit
ASCII writes for these two modes. Other formatter options fall back to the
standard Debug builders. The builder declarations intentionally leave output
content unconstrained, so there is no formal content guarantee for those
fallback cases. Output guarantees apply only when the call returns `Ok(())`
and `append_sink` holds on entry; `Err` output and partial writes are
unconstrained. A sink that inserts indentation, transforms text, or otherwise
fails to faithfully append successful writes is outside the guarantee. No
initial-empty-output assumption is made. The pinned Debug source references
and finite native comparisons do not prove standard-library equivalence.

The declarations do not specify non-ASCII UTF-8 conversion, general
`SystemTime` addition, arbitrary timestamp differences, platform behavior
outside 64-bit Linux or macOS arm64, arbitrary hasher implementations, or standard-library
internals. Existing creusot-std models for `Duration`, `Result`, slices,
integers, and string views remain trusted dependencies as well.

The date arithmetic, parser and formatter kernels, Hash and Debug application
implementations, Error display/message construction, and application-level
lemmas remain ordinary untrusted code and proof obligations. `RawDate`'s
derived Debug implementation is outside the selected public Debug proof.
The trim and byte-content uniqueness
interface lemmas are proved, not trusted declarations. Adopting these boundary
assumptions does not widen their contracts or make the date core trusted. The
independent trial's native tests and production custom-writer, error-display,
typed-hash, and Debug regressions are sanity checks on examples; they are not proofs
of these assumptions. See its README and
[pinned Rust source references](stdlib-reference.json) for reviewed source
locations and hashes.

## macOS arm64 source review

The existing time contracts are also enabled for macOS arm64 after reviewing the pinned Rust 1.91.0 and nightly-2026-06-22 implementations. [platform-review/review.json](platform-review/review.json) records the source hashes and findings; the source copies are inputs to the new proof run. Both implementations use the Unix normalized Timespec representation for SystemTime. Epoch addition under the existing date bound fits the i64 seconds field; public Add delegates to checked addition. The Apple-specific pre-epoch external-timespec normalization does not change this bounded epoch-addition path. The duration_since model and all existing formatter, hashing, and error conditions remain unchanged. These are reviewed conditional models, not proofs of standard-library code, arbitrary OS clocks, or all macOS targets. New native differential evidence is recorded separately.
