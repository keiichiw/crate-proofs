# httpdate 1.0.3: released source and verification-fork correspondence

The formal proofs describe the annotated fork, not the unmodified crates.io
artifact. This directory supplies a reproducible release identity, a source
transformation audit, and finite native observations connecting the two. None
of these observations proves semantic equivalence for every input or proves the
standard library.

## Release identity

[release.json](release.json) records the checksum returned by the captured
[crates.io version API](https://crates.io/api/v1/crates/httpdate/1.0.3), the
[captured response](registry-metadata.json), and the archive URL. The downloaded
`httpdate-1.0.3.crate` SHA-256 is
`df3b46402a9d5adb4c86a0cf463f42e19994e3ee891101b1841f30a545cb49a9`, matching
that registry checksum. Its embedded VCS SHA is
`638da761065df8b67282b0a1d139c0a7e4a02429` (published 2023-08-13).

The fork was copied from the later Git commit
`53df52094835dd85aca70e23b9f384abcf843f7f` (2024-12-10). The two release
runtime files, `src/lib.rs` and `src/date.rs`, match both Git commits byte for
byte. The saved [trial date reference](../trial/reference/date.rs) also matches
the released `src/date.rs`. The release and copied Git commits are distinct;
the runtime-source identity is established by comparing actual bytes.

[reference/](reference/) preserves those two unchanged Rust sources, both
license files, the original package manifest, and VCS metadata. Its separate
[build manifest](reference/Cargo.toml) changes the package name to
`httpdate-release-reference` and omits development-only dependencies so it can
link alongside the fork. It leaves release Rust code unchanged. That wrapper
manifest is not represented as the published crate manifest.

## Source and API audit

The following mapping records the material executable changes at proof source
baseline `42c3027836b797e8acc1bc4cd199873f8bd6f169`. The release originals are
[lib.rs](reference/src/lib.rs) and [date.rs](reference/src/date.rs); destination
links point to the actual verification fork. The listed behavior is the intended
correspondence, supported by source review and the separately recorded native
comparisons. It is not a formal proof between the two programs.

| Upstream element | Fork implementation / transformation | Correspondence evidence and limits |
| --- | --- | --- |
| Public `HttpDate` record; derived Copy, Clone, PartialEq and Eq | [date.rs](../../crate/src/date.rs): same private fields and types; separate permissive `RawDate`; explicit Clone and seven-field equality; checked validity invariant in the proof configuration | Native public constructors retain the flat 8-byte representation. Compile checks retain Copy/Clone/Eq/Ord/PartialOrd/Hash/Display/Debug, time conversions, FromStr and Send/Sync/Unpin. Sampled comparisons and exact-copy checks supplement fork invariant/bridge proofs. Size agreement does not establish Rust ABI stability. |
| `From<SystemTime>` Gregorian conversion | [date.rs](../../crate/src/date.rs): original `duration_since`/`expect` and year-limit panic remain in the adapter; calendar arithmetic extracted into `from_unix_seconds`; assertions/lemmas only in `cfg(creusot)` | Reviewed March-origin constants, cycle corrections, month table, weekday calculation and field assignments; every supported civil day's representative instant and time boundaries compared. Both versions panic before Epoch and at/after year 10000. The unconditional trait refinement remains open. |
| `From<HttpDate> for SystemTime` and `Ord`/`PartialOrd` | [date.rs](../../crate/src/date.rs): original leap/year/day arithmetic extracted into `to_unix_seconds`; reverse adapter adds Duration to Epoch; ordering compares integer seconds instead of reconstructing SystemTime | Bidirectional native conversion at every sampled day; adjacent/equal ordering pairs and whole-second floor checks. Fork timestamp/validity lemmas are proved under the recorded time model; no claim about unsupported platforms. |
| Private `HttpDate::is_valid` | [date.rs](../../crate/src/date.rs): same scalar range checks, then raw whole-second round trip and seven-field comparison instead of public SystemTime round trip | Invalid-calendar/weekday grid and valid-day samples; fork validator contract characterizes `valid_calendar`. Private raw records deliberately permit grammar-valid but calendar-invalid fields. |
| `FromStr` and public `parse_http_date` | [date.rs](../../crate/src/date.rs) and [lib.rs](../../crate/src/lib.rs): preserve non-ASCII rejection then ASCII trim; extract byte parser and replace `or_else` with ordered short-circuit `match`; `Result::map` becomes explicit matching | Public Result outcomes, FromStr results, normalized output and Error messages compared on the corpus. Parser order remains IMF → RFC850 → asctime, then calendar validation. All-input functional proofs concern the fork's stated grammars, not cross-program equivalence. |
| IMF/RFC850/asctime raw parsers | [date.rs](../../crate/src/date.rs), [rfc850.rs](../../crate/src/date/rfc850.rs), [asctime.rs](../../crate/src/date/asctime.rs): move legacy routines into children, use scalar/tuple byte checks instead of byte-string slice patterns | Reviewed field offsets, lengths, delimiter sets, month/weekday maps, digit calls and error paths. Mutated fixtures, fixed-pivot years and malformed inputs compared. The RFC850 separator between year and time remains unchecked, including accepted `...94x08:...`. Strict RFC conformance is not claimed. |
| `toint_1`, `toint_2`, `toint_4`, `is_leap_year` | [date.rs](../../crate/src/date.rs): add surrounding annotations; complete runtime function text unchanged | Capture checker compares complete function texts byte for byte and records their hashes. No comment/annotation stripping or token-normalization heuristic is used for this check. Native digit exhaustion remains in the existing 34-test suite. |
| Date Display and `fmt_http_date` | [date.rs](../../crate/src/date.rs) and [lib.rs](../../crate/src/lib.rs): extract original 29-byte layout as `imf_bytes`; use fully qualified fmt::Write dispatch; construct String directly rather than `format!` | Release/fork strings agree on every sampled day and fractional-second boundaries; Display writer chunk/error/panic observations agree on selected dates. Allocation behavior, cost and allocation failures are not compared or proved equivalent. Formal content is conditional on successful faithful appending. |
| Derived `Hash` | [hash.rs](../../crate/src/date/hash.rs): explicit typed hashing of sec/min/hour/day/mon (`u8`), year (`u16`), wday (`u8`) | Typed call traces, DefaultHasher finishes and native default `hash_slice` traces agree on sampled dates. Formal Hash claims require a supported nonpanicking hasher, same hasher type and complete initial model state. No collision freedom, cross-version digest stability, or formal hash_slice claim. |
| Derived public Date/Error Debug | [debug.rs](../../crate/src/date/debug.rs), [debug_support.rs](../../crate/src/debug_support.rs), [lib.rs](../../crate/src/lib.rs): checked explicit plain normal/pretty formatting; standard-builder fallback for other options; pretty decimal helper uses one write | 15 formatting variants, three nested variants and normal/pretty/combined writer traces compared. Native observations cover transformed/indenting writers; formal exact content covers only plain options, Ok and a faithful append sink. Private RawDate Debug is excluded. |
| Error Display, default Error methods and `From<Error> for io::Error` | [lib.rs](../../crate/src/lib.rs): fixed ASCII message with qualified writer dispatch; explicit source/cause/description preserving defaults; `io::Error::new(Other,e)` remains unchanged | Actual released Error type used as reference. Native message/default methods, IO kind, get_ref/downcast/into_inner checks; fork IO content guarantee depends on direct concrete-payload constructor model, while dynamic observers are native-only. |

Other changes include `creusot-std = "=0.13.0"`, the fork's Rust 1.91 minimum,
proof-only stdlib specifications/logic, and regression tests. The original
Rust 1.56 MSRV, compilation on every target, performance, ABI guarantees,
allocation identity, and arbitrary external callback behavior are not established.

## Reproduction and saved observations

The standalone comparison needs Rust 1.91.0 (selected by the repository's toolchain file), a native linker, Python 3, and Bash. It does not activate the formal verification environment or read a formal manifest. From the repository root:

```bash
bash httpdate/1.0.3/scripts/check-correspondence.sh
```

Cargo uses `--locked --release` and may download locked dependencies on first use. To require an existing cache, set `CARGO_NET_OFFLINE=true`. A successful run writes `native-manifest.json`, source fingerprints, counters, and logs under the printed `verif/correspondence-*` directory. It does not replace the formal-bound evidence pointer.

After producing a formal proof for the same source, bind that completed native run separately:

```bash
source scripts/activate.sh
python3 httpdate/1.0.3/scripts/capture-correspondence.py --bind /absolute/path/to/correspondence-RUN
```

Binding verifies the saved native artifact hashes and current comparison inputs, then checks the formal manifest against current formal source/tool hashes. It preserves the native compiler and host identity, saves a formal-bound manifest, and promotes `evidence/latest` only after all checks pass. Existing evidence is preserved. Native observations remain distinct from formal proof.

To additionally compare the actual checksum-pinned archive, explicitly fetch
it with `check-correspondence.sh --fetch`, or supply a downloaded archive with
`--archive /path/to/httpdate-1.0.3.crate`. `--check-origin` additionally checks
the clean `/workspace/httpdate` checkout and release Git object, when available.
None of these operations records or publishes a proofs.rs report.

The independent [workspace](Cargo.toml) links the released and verified crates in the same native executable. [Harness source](src/main.rs) and [lockfile](Cargo.lock) make the corpus reproducible. The [coverage report](../coverage.md) owns current run status and provenance-check modes. The corpus contains these observation groups:

| Observation group | Count | Sampling / meaning |
| --- | ---: | --- |
| Supported civil days | 2,932,897 | Exactly one instant, 12:34:56, on each day from Epoch through 9999-12-31; public formatting, parsing, constructors and reverse conversion |
| Boundary/subsecond instants | 42 | 14 selected seconds × nanos 0, 1, 999999999 |
| Additional parser inputs | 132,353 | Every ASCII replacement at every position of eight fixtures; truncations; whitespace/non-ASCII; invalid-calendar/time grid; all 100 fixed-pivot years; preserved separator quirk; 66,048 deterministic ASCII strings of lengths 0..128 |
| Comparison pairs | 8,868 | Equal, preceding and following seconds on every 997th day plus 14 boundary fixtures; equality/order/PartialOrd and comparison operators; associated clone/hash observations |
| Formatting observations | 90 | 15 Debug option variants + three nested variants, each on four dates and one actual Error |
| Writer observations | 2,560 | Same five values × four Display/Debug formats × 64 failure thresholds × error/panic modes; attempted chunks and outcomes compared |
| Out-of-domain panic observations | 8 | Four unsupported timestamps × forward-conversion/formatting operations; both programs panic |
| Error/IO observation group | 1 | Defaults, message, Other kind and both types' payload downcast/ownership observers |

Counts describe observation groups, may overlap, and are not a count of APIs,
formal goals, or unique tested input strings. Seed: `0x6874747064617465` with
xorshift shifts 13/7/17. The daily sample does not enumerate every supported
second, all parser strings, all formatter options or all callbacks. Callback
panics exercised here are finite compatibility observations; proof panic claims
still depend on the trusted callback contracts.

These observations are separate from the selected formal results in
[coverage](../coverage.md). No submission draft is currently maintained.
