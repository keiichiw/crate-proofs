# httpdate 1.0.3 API inventory and feasibility notes

Inventory of `crate/src/lib.rs`, `crate/src/date.rs`, the installed Creusot 0.13.0 sources, checked-in examples, and recorded feasibility trials. “No support found” means no applicable spec/example was found in those sources; it does not prove the compiler cannot translate or reason about a call. Trial outcomes below are evidence only for their stated targets and assumptions.

## Public API and Creusot exclusions

| Public item | Native behavior | Creusot configuration |
| --- | --- | --- |
| `HttpDate` | Public struct; fields are private. Derives `Copy`, `Clone`, `Debug`, `Hash`, `Eq`, `PartialEq`; manual `Ord` / `PartialOrd`. | Type and fields remain, but `Eq` / `PartialEq` derives and `Ord` / `PartialOrd` impls are removed. `Hash` and `Debug` derives remain in source. |
| `Error` | Opaque public unit-like error (`Error(())` has a private constructor), derives `Debug`; implements `std::error::Error`, `Display`, and conversion into `io::Error`. | Only the type and `Debug` derive remain. The error trait, display, and I/O conversion impls are `cfg(not(creusot))`. |
| `parse_http_date(&str) -> Result<SystemTime, Error>` | Parses IMF-fixdate, RFC850, and asctime after ASCII check and trimming; rejects calendar-invalid dates. | Entire function is `cfg(not(creusot))`. |
| `fmt_http_date(SystemTime) -> String` | Converts and formats IMF-fixdate. | Entire function is `cfg(not(creusot))`. |
| `From<SystemTime> for HttpDate` | Native wrapper rejects pre-epoch and year 10000+, truncates fractional seconds, then calls `from_unix_seconds`. | Wrapper remains `cfg(not(creusot))`; pure seconds-to-calendar core is shared and specified. |
| `From<HttpDate> for SystemTime` (and blanket `Into<SystemTime>`) | Native wrapper calls `to_unix_seconds` then adds whole-second `Duration` to epoch. | Wrapper remains `cfg(not(creusot))`; pure calendar-to-seconds core is shared and specified. |
| `FromStr`, `Display` for `HttpDate` | Parsing/validation and IMF-fixdate formatting. | Both impls are `cfg(not(creusot))`. |
| `Eq` / `PartialEq`, `Ord` / `PartialOrd` for `HttpDate` | Equality is structural over fields; ordering compares converted `SystemTime`. | Trait impls are excluded as above. |

The current production proof scope includes the digit helpers; IMF parser; pure IMF byte formatter; forward and reverse calendar conversion; leap predicate; exact `valid_calendar` characterization by `is_valid_date`; civil-day injectivity; calendar and seconds roundtrips; shared byte parsing; and the IMF-specific successful parse roundtrip. See `verification/coverage.md` and the current run manifest for authoritative target and goal counts. The range-only parser milestone is historical, not the current contract.

The asctime parser has a strong byte-grammar and field-encoding contract and its focused proof closed 14 goals. Its current Coma and proof JSON are under `verification/evidence/latest/asctime/parse_asctime/`, with matching logs, versions, and source hashes in the full-run manifest; native differential coverage is in `crate/src/date/asctime_tests.rs`.

The RFC850 raw parser now has a fully proved grammar and seven-field encoding contract. Success implies the weekday, day, month, year, hour, minute, and second values encoded by the input; `Err` holds iff the input is outside that grammar. Byte 9 of the suffix between the two-digit year and hour is intentionally unconstrained because that matches the upstream source behavior. The focused source-level run closed 28 parser goals plus 5 weekday-helper goals. The fresh full selected-core run also closed; use `verification/coverage.md` and its matching manifest for authoritative aggregate status and counts. Check `verification/trial/method.md` for trial design and other boundaries.

The production parser boundary recognizes syntax and extracts raw fields. Calendar validity is a separate predicate used by the public parsing layer; raw records can be invalid calendar dates. Do not conflate the parser's contract with a valid public `HttpDate` or claim full public API verification. The native `HttpDate` equality model has seven fields including weekday, while native `Ord` compares chronological time and ignores weekday. A future integrated model should distinguish raw parser records from validated public values, for example with separate `RawDate` and validated date types.

Positive trait experiments use abstract three-field `Date` models and are not proofs of `HttpDate`'s actual traits. The equality model closes 6 goals across 5 Coma files; the chronological order model closes 21 goals across 17 files, including generated callees. A separate conditional standard-library model has 18 goals across 5 targets and uses eight trusted specification assumptions for 64-bit Linux. Keep those assumptions explicit and scoped to the trial model; they are not production API specifications. Trait probe negatives for `SystemTime`/string/Error facilities and `Hash` remain unresolved. `Formatter::write_str` translation/call goals closed, but no postcondition describes emitted text.

The native regression suite has 24 tests, including a differential conversion sample at 12:34:56 on each of the 2,932,897 supported civil days. The RFC850 differential test covers all seven weekday-prefix lengths with valid November 1994 dates, both year-pivot branches, malformed lengths, the unchecked year/hour separator, and every ASCII replacement at each position in two valid fixtures. These tests establish observed agreement for those inputs, not exhaustive time-of-day equivalence or formal equivalence to upstream. Keep native results separate from proof status. The proof methodology, trial boundaries, and links to detailed outputs are documented in `verification/trial/method.md`.

Future `proofs.rs` registration for the public API has not been performed. Do not log in, publish proof results, or push changes without explicit authorization.

## Observable panic and precision behavior

- `HttpDate::from(SystemTime)` calls `duration_since(UNIX_EPOCH).expect(...)`, so any time before the epoch panics.
- It then calls `Duration::as_secs()`, which discards fractional seconds. `HttpDate` stores second precision; converting back uses `Duration::from_secs`. Values within a second map to its start.
- The conversion panics when epoch seconds are `>= 253402300800`, the start of year 10000. The final second of year 9999 (`253402300799`) is allowed.
- `to_unix_seconds` assumes bounded fields, including month 1..12 and year 1970..9999, and has an unreachable fallback for other months. `imf_bytes` similarly assumes bounded fields and has unreachable fallbacks for weekday and month. Fields are private; safe public construction uses `From<SystemTime>` or calendar-validated `FromStr`.
- `fmt_http_date` inherits `From<SystemTime>`'s panic domain. `Display` converts the fixed ASCII `[u8; 29]` from `imf_bytes` using `from_utf8(...).unwrap()`; the pure formatter's proof specifies ASCII, but the wrapper itself remains native-only.

Native regression cases for API expansion should pin the pre-epoch panic, seconds `253402300799` versus `253402300800`, and subsecond truncation (including just-before-boundary fractional inputs). These clarify observable behavior; they do not change it.

## Creusot 0.13.0 library support audit

The inspected installed source is `/workspace/creusot` at commit `318615be3b8bbc60d1f6d52469ba5c0bdebed4f1`, particularly `creusot-std/src/std/` and `tests/should_succeed/`.

| Facility used by httpdate | Evidence in installed Creusot std | Practical status for this crate |
| --- | --- | --- |
| `Duration` | The installed `std/time.rs` gives it an integer-nanosecond view and specs for construction, `as_secs`, subsecond accessors, checked arithmetic, add/sub. The installed duration success test exercises these specs. | Positive support for pure seconds/nanoseconds adapters. `SystemTime` is a different type. |
| `SystemTime`, `UNIX_EPOCH`, `duration_since` | The installed standard library model specifies `Duration` and (under `std`) `Instant`, but not the `SystemTime` semantics needed by this crate. A separate conditional model experiment supplies eight trusted specification assumptions on 64-bit Linux. | That conditional model is an isolated trial, not a production API specification. Native `SystemTime` wrappers remain outside the production proof scope. |
| `Formatter::write_str` | The installed `std/fmt.rs` declares an extern spec for `write_str`, but gives it no postcondition about emitted text. | The call is declared, but this is not a usable output-content contract for proving `Display` formatting. |
| `Display` | No `Display` trait specification or example impl found in installed `creusot-std/src` or `tests/should_succeed`. `std/fmt.rs` only covers `Formatter` methods. | No behavioral proof support found. Extract a pure byte formatter and leave `Display` as a thin adapter for the trial. |
| `str::len`, `split_at`, string model | The installed `std/string.rs` models `str` as `Seq<char>`, defines `to_bytes`, and specifies `len` / `split_at`. | Some useful foundations exist, but they do not supply the HTTP parser’s needed operations below. |
| `str::is_ascii`, `str::trim`, `std::str::from_utf8` | No method/function specs or proof examples found by searching installed `creusot-std/src` and `tests/should_succeed`. | No support evidence found. Keep these in native adapters or replace the core boundary with explicitly specified byte/ASCII operations. Do not silently assume Rust behavior in contracts. |
| `PartialEq`, `Ord` | The installed `std/cmp.rs` supplies generic specs in terms of `DeepModel`, `PartialOrdLogic`, and `OrdLogic`; integer primitives are also covered. | Trait machinery exists. `HttpDate` has no production Creusot `DeepModel`; native `Ord` is chronological and ignores weekday. A validated date/time model would be needed to verify production ordering. |
| `Hash` | No `Hash` trait spec or hasher model found in the installed std source. `HashSet` / `HashMap` use `Hash` as a bound, which is not evidence that `Hash::hash` semantics are specified. | No support evidence found for proving the derive’s hash behavior or equality/hash law. Treat as an explicit open boundary. |
| `std::error::Error`, `io::Error`, conversion from `Error` | The installed `std/io.rs` only specifies private `_print` / `_eprint`; no `io::Error` or `std::error::Error` specs were found. | No support evidence found. The opaque error value and wrapper conversions can remain outside the pure parser core. |
| `Debug` | `std/fmt.rs` declares several formatter debug methods for `Debug` output. | Some debug formatting hooks exist; they do not imply `Display`, `Hash`, or `io::Error` support. |

The absence entries above are source-search findings, not claims that every call necessarily ICEs or fails to compile. Direct translation/support would require an isolated compiler/proof trial before making a stronger statement.

## Trial methodology and remaining boundaries

The broader production proof now covers calendar arithmetic, formatter bytes, parser cores, and validity relationships. Use `verification/trial/method.md` for the evidence map and `verification/coverage.md` plus the current manifest for the selected production targets and totals; avoid copying changing aggregate counts into this inventory.

The native 12:34:56 comparison samples every supported civil day from 1970-01-01 through 9999-12-31, with separate boundary and wrapper regressions. It does not exhaust all times of day. Differential parser tests compare observed behavior on fixtures and mutations; they do not prove upstream equivalence.

The standard-library probe outcomes are in `verification/trial/probes/run.sh` and `verification/trial/probe-results/summary.json`. `Duration`'s modeled nanoseconds reconstruct successfully. The `SystemTime`, UTF-8, and string ASCII/trim semantic goals remain open. `Formatter::write_str` goals concern translation/panic behavior only; there is no emitted-text postcondition. These results do not establish public API behavior.

The remaining whole-API boundaries include the native `SystemTime` and string adapters, `Display` output semantics, `Hash`, I/O error traits, and production `HttpDate` trait models. Any future report should list the pure functions proved, adapter boundaries left native, trusted library assumptions, goal counts from the current manifest, and native test outcomes separately.

One proof-debugging lesson from the RFC850 effort: Why3 tree indices and labels such as a month name do not reveal which runtime branch a VC represents. Inspect the actual prover input saved by the timeout session, including its hypotheses and goal. For bytewise grammar reasoning, a structural sequence inequality may require a separately checked extensional-equality bridge in the helper contract before pointwise byte facts can follow.
