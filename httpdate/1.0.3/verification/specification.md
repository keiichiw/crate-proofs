# Verified surface and contracts

The selected scope is the verification fork's byte / integer parser and calendar core, together with some wrappers / traits connected to public `HttpDate`. This document describes contract scope. Refer to [coverage.md](coverage.md) and the manifest updated after each run for proof targets and results. Do not treat an old manifest or a past total target count as evidence for the current implementation.

## `RawDate` and public `HttpDate`

Raw parsers and internal calendar calculations use private `RawDate`, which can represent calendar-invalid values. Its seven fields are second, minute, hour, day, month, year, and weekday. A raw parser may return values such as `99` seconds, day `00`, or a nonexistent leap day if they satisfy only the numeric grammar. Success from a raw parser does not imply calendar validity.

Public `HttpDate` also has the same seven fields in a flat private record, but its checked Creusot invariant requires `valid_calendar`. `as_raw` is a checked bridge that preserves all seven fields; `from_raw` is a checked bridge that constructs a public value under the `valid_calendar` precondition. Public constructor paths validate before creating a value. There is no contract that directly constructs an invalid `HttpDate`.

## Digits, syntax, and calendar

An ASCII digit is a byte value from 48 through 57. `toint_1` accepts any byte; `toint_2` and `toint_4` work on slices of length at least 2 and 4, respectively. They succeed only if all relevant leading bytes are digits, and return the corresponding decimal value. Trailing bytes do not participate in conversion. Short slices are outside the preconditions of `toint_2` / `toint_4`.

Raw-parser contracts describe accepted syntax and the correspondence of all seven fields on success. No raw parser has an input precondition; slice bounds and safety of numeric operations are also verified.

- IMF-fixdate accepts length 29, weekday and month abbreviations, separators, `GMT`, and decimal digits at fixed positions. `imf_encoding(s,d)` expresses the content correspondence between the input and seven fields.
- asctime has length 24, weekday and month abbreviations, a time, and a four-digit year; the day is written as two digits or a space followed by one digit. `asctime_encoding(s,d)` expresses the content correspondence.
- RFC850 selects a weekday-name prefix by its full name, then parses the remaining 22 bytes for day, month, year, and time. For a two-digit year less than 70 it adds 2000; otherwise it adds 1900. `rfc850_encoding(s,d)` expresses the content correspondence.

**The RFC850 implementation does not check the byte between the two-digit year and the time.** For example, it accepts `Sunday, 06-Nov-94x08:49:37 GMT`. The contract does not constrain that byte either. This is the acceptance behavior of the pinned upstream implementation; no claim of strict HTTP-standard conformance is made.

The supported Gregorian range is `0 <= seconds < 253402300800`, from Unix Epoch through the end of year 9999. A year is a leap year if divisible by 4, except years divisible by 100 must also be divisible by 400. `gregorian_day(d)` defines the day number with 1970-01-01 as 0. `valid_calendar(d)` requires:

- Seconds and minutes below 60; hour below 24.
- Year in 1970..9999, month in 1..12, and day within the actual length of the month.
- Weekday equal to `(gregorian_day(d) + 3) % 7 + 1`, where Monday is 1 and Sunday is 7.

`from_unix_seconds` returns, for a supported second count, a valid date, day number `seconds / 86400`, and seconds within the day `seconds % 86400`. `to_unix_seconds(RawDate)` assumes numeric ranges for each field and returns `gregorian_day(d) * 86400 + hour * 3600 + min * 60 + sec`. This helper alone does not rule out February 31 or a weekday mismatch.

`civil_day_injective` is a checked lemma, not a trusted assumption, that proves uniqueness of valid year-month-day values. `seconds_roundtrip`, `calendar_roundtrip`, and `is_valid_date` specify second round-tripping, seven-field round-tripping of valid dates, and calendar-validity classification for all inputs, respectively.

## Parser and public parse API

`parse_date_bytes` tries raw parsers in the order IMF → RFC850 → asctime, then validates the calendar. On success it returns a valid `RawDate` and seven fields corresponding to one of the three formats. On failure, any `RawDate` described by an encoding of one of the three formats is calendar-invalid. This failure contract covers all three formats. Checked `encoding_laws` in the RFC850 / asctime child modules establish each encoding's input length and uniqueness of the raw record corresponding to that input.

Success from `FromStr for HttpDate` and `parse_http_date` describes a valid date and corresponding timestamp matching the input encoding after ASCII trimming. On failure, if the trimmed content corresponds to an encoding in any of the three formats, its raw record is calendar-invalid. Checked `trim_unique` and `bytes_unique` lemmas connect reasoning about ASCII trim / byte content to the parsed slice. These are not trusted assumptions.

## Formatter and `fmt_http_date`

`imf_bytes(RawDate)` assumes field ranges, creates 29 ASCII bytes, and satisfies `imf_encoding`. `imf_roundtrip` and `valid_imf_roundtrip` specify round-tripping between the raw formatter and parser.

`HttpDate::imf_string` converts these 29 bytes to ASCII UTF-8 `String` and preserves canonical IMF content. `fmt_http_date(SystemTime)` assumes `0 <= time_ns(t) < 253402300800000000000` and returns a valid calendar date, the timestamp's second portion, and canonical IMF content. Subsecond precision is truncated.

Content guarantees for `Display for HttpDate` and `Display for Error` apply only when the result is `Ok(())` and `append_sink` is true. On success, HttpDate appends characters matching canonical IMF encoding; Error appends exactly `string contains no or an invalid date`. No content guarantee is made for arbitrary sinks, partial writes on `Err` are unconstrained, and the initial output is not assumed empty. See the [standard-library assumptions ledger](stdlib-assumptions.md) for details.

## Public type traits and time conversions

The `PartialEq` implementation compares all seven fields. Its Creusot refinement relates the comparison result to the timestamp `DeepModel` of public values; checked `valid_datetime_injective` shows that two valid values with equal timestamps have equal seven fields. `Ord` compares results from shared `to_unix_seconds`, and `PartialOrd` always wraps that result in `Some`. These implementation bodies and refinements are in the focused proof scope.

`Clone` for `HttpDate` and `RawDate` returns `*self` and has a contract that the result equals the original value.

`Hash for HttpDate` is implemented explicitly, not derived. It preserves the field order and primitive typed dispatch of the original derive. It hashes `sec`, `min`, `hour`, `day`, and `mon` in order as `u8`, then `year` as `u16`, and finally `wday` as `u8`. The Creusot postcondition specifies the model state after applying the corresponding typed `hash_step_u8` / `hash_step_u16` operations in this order. The contract requires `supported_hasher::<H>()` and does not apply to arbitrary `Hasher` types.

`supported_hasher` is a type-level assumption requiring deterministic, total, non-panicking `write_u8`, `write_u16`, and `finish`, plus enough model state to predict future operations and results. The checked lemma relating hash results for equal `HttpDate` values assumes the same hasher type and the same complete initial model state. `DefaultHasher::new` is a concrete witness for a supported hasher starting from model state 0. In the pinned Rust source it creates `SipHasher13` with fixed keys `(0, 0)`. Native tests illustrate typed call sequences and consistency for Eq values, but do not justify treating the write history as the state.

Hash model state and digest are not injective, and no collision-free guarantee is made. No claim is made that DefaultHasher digest values stay stable across Rust versions. `Hash::hash_slice` is outside this formal specification. Do not generalize the pinned source's default implementation or native test results into the production Hash contract. Native differential tests are finite observations; the selected Debug contract and its scope are described below.

The normal path of `From<SystemTime> for HttpDate` constructs a calendar value for times from the Epoch and before year 10000. Existing behavior outside that range is to panic before the Epoch and from year 10000 onward. The trait method refinement is not closed as an unconditional conversion and makes no guarantee beyond this panic boundary. Native tests check panics and subsecond truncation.

`From<HttpDate> for SystemTime` computes `UNIX_EPOCH + Duration` under the public invariant and has a timestamp refinement. It depends on the supported domain and the Epoch-addition conditions in the standard-library assumptions ledger.

`system_time_roundtrip` is a harness specifying a round trip to the corresponding whole-second timestamp. It guarantees preservation of time truncated to whole seconds and is recorded with the other selected functions in fresh-run evidence.

## Trust boundary, evidence, and exclusions

Application-level `RawDate` / `HttpDate` fields, calendar calculations, parser / formatter kernels, wrappers, and trait bodies are not trusted. The standard-library boundary uses 41 conditional declarations / models. Refer to the [ledger](stdlib-assumptions.md) for target platforms and domains, each assumption, and Formatter limitations. This does not prove the Rust standard-library implementation itself.

## Error trait and IO conversion

`Error::source` and deprecated `Error::cause` return `None`. Deprecated `Error::description` returns exactly the 40-character string `description() is deprecated; use Display`. Their checked contracts are verified under an ASCII `from_utf8` boundary model. The scope covers these three method implementations, not every standard-trait method, trait-object interface, or unstable `provide` API.

Under an append sink, `Display for Error` has a checked contract to append the fixed ASCII string `string contains no or an invalid date` only when it succeeds. The body and refinement of `From<Error> for io::Error` specify that the kind is `Other` and the same concrete `Error` payload is retained. This depends on the ledger's direct-payload `io::Error::new` assumption. Native regression tests also observe the payload using `get_ref`, dynamic downcast, and `into_inner`, but these APIs are outside the formal specification and proof scope.

## Public `Debug`

`Debug for HttpDate` does not fully delegate to the standard builder; it distinguishes normal / alternate pretty mode and explicitly writes the seven fields. Only the public type is in scope; derived Debug for private `RawDate` is excluded. The content refinement applies when formatter flags are `0` (normal) or `4` (alternate), width / precision / alignment are `None`, fill is a space, and the fmt call returns `Ok(())` with `append_sink` true.

Under these conditions, HttpDate output contains each field name and decimal value in order: `sec`, `min`, `hour`, `day`, `mon`, `year`, `wday`. Normal mode uses a single line with standard field separators; alternate mode uses four-space indentation and a newline for each field. Under the same conditions, `Error` prints `Error(())` in normal mode and `Error(\n    (),\n)` in alternate mode. For `u8` / `u16` Debug and unit Debug, the std model specifies successful decimal digits or `()`, and requires preservation of formatter options and the append-sink condition.

When options do not satisfy `plain_options`—other flags, width, precision, alignment, or fill—the application Debug body falls back to the standard Debug builder. Its extern specifications have no content postcondition, so the resulting string has no formal guarantee in those cases. Every content guarantee is conditional on `Ok(())` and faithful `append_sink`; partial output on failure is unconstrained. A sink that inserts indentation or transforms text is not a faithful append sink. Initial output is not assumed empty. Pinned-source review and finite native tests do not prove general formal equivalence with the standard implementation.

The main crate's Creusot proofs, native tests, and upstream differential tests are reported as separate evidence. Native differential tests observe agreement on finite inputs and are not formal equivalence with upstream. Inherited / observer methods of `io::Error` are outside formal proof scope. The HttpDate and Error Debug contracts above apply only to selected verified targets; they do not guarantee Debug semantics for other formatter options. Public API `proofs.rs` and SARIF registration have not been done. Until the manifest is updated, do not claim new overall target counts or full-run success.
