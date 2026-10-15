# Upstream source provenance

- Upstream repository: https://github.com/pyfisch/httpdate
- Source-copy commit: `53df52094835dd85aca70e23b9f384abcf843f7f`
- Commit time: 2024-12-10T16:42:55Z
- Source-copy tree: `/workspace/httpdate`
- Target path: `httpdate/1.0.3/crate/`
- Package name and version: `httpdate` 1.0.3
- Declared license: `MIT OR Apache-2.0`; `LICENSE-MIT` and `LICENSE-APACHE` are included.
- Copy method: extracted Git-managed files from the commit above with `git archive`. The upstream working tree was not modified.

This directory is a verification fork and differs from the public crates.io package. It adds Creusot contracts, checked ghost lemmas, a type boundary, conditional extern models for the standard library, and verification tests. Follow the [specification](specification.md), [assumptions ledger](stdlib-assumptions.md), and latest coverage / manifest for the source scope and conditions. The digit-conversion helper's computational body is unchanged.

## Correspondence with the crates.io distribution

The SHA-256 of the crates.io 1.0.3 distribution archive is
`df3b46402a9d5adb4c86a0cf463f42e19994e3ee891101b1841f30a545cb49a9`, matching the
registry checksum obtained. The distribution's VCS commit is
`638da761065df8b67282b0a1d139c0a7e4a02429`. It differs from the source-copy commit
above, but `src/lib.rs` and `src/date.rs` in both commits and the distribution are
byte-for-byte identical.

The [provenance record](correspondence/release.json), [captured registry metadata](correspondence/registry-metadata.json),
unmodified [distribution source](correspondence/reference/), and [API / implementation correspondence table](correspondence/README.md) are saved.
The independent native-comparison workspace runs both crates' public APIs and records
the [comparison results and source/tool fingerprints](correspondence/evidence/latest/manifest.json).
This is not a formal equivalence proof between the distribution and the fork.

To repeat the check, run `bash httpdate/1.0.3/scripts/check-correspondence.sh`. It runs independently of formal evidence, using fixed local sources and the lockfile; missing Cargo dependencies may be downloaded. Formal evidence binding is a separate `capture-correspondence.py --bind RUN_DIRECTORY` step; explicitly use `--fetch` to fetch the archive again or `--archive` to check an existing archive. No submission draft is currently maintained; proofs.rs recording remains a separate task.

## Changes in the verification fork

The implementation separates permissive `RawDate` for raw parsing and calendar-core work from public flat seven-field `HttpDate`, which has a checked valid-calendar invariant. `as_raw` / `from_raw` are checked bridges at this boundary. `FromStr` and the public parser verify trim / byte-content bridges; the parse kernel specifies calendar invalidity on failure for encodings in all three formats. Checked `encoding_laws` in the RFC850 / asctime child modules pass each grammar's length and uniqueness to the kernel.

The integer calendar core was extracted from the original SystemTime conversion, a 29-byte formatter core from Display, and a byte parser kernel from FromStr. The upstream calendar algorithm and raw-parser evaluation order were preserved; the RFC850 / asctime parsers were moved to child modules under `src/date/`. Month, weekday, and similar comparisons use scalar bytes and tuples to avoid Creusot 0.13 translation issues with byte-string / slice patterns. `Result::or_else` was made an explicit `match` with the same order and short-circuit behavior.

Public-value `Eq` compares the original seven fields, while `Ord` compares shared integer seconds rather than rebuilding `SystemTime`. `PartialOrd` follows `Ord`. The public representation of `HttpDate` remains the original flat seven-field record (8 bytes in size), with Debug / Hash field representation unchanged. The public formatter directly constructs canonical IMF `String` output through `imf_bytes` and `imf_string`. Error's Display passes explicit ASCII bytes to `<Formatter as fmt::Write>::write_str`. Rust source review confirmed that both inherent `Formatter::write_str` and the trait implementation independently delegate to the buffer's `write_str`, but this is not a standard-library proof. Fixed source, line, and hash information is in the [reference ledger](stdlib-reference.json).

The upstream `src/date.rs` was saved unchanged as [trial/reference/date.rs](trial/reference/date.rs) for comparison. Its SHA-256 is `87e7de1394f6b0d37128bfbf5943e256c886c35ed3f9078d15a08309c2206c69`. It is used as the reference implementation in native differential tests and is distinct from the verification fork. Behavior was compared for representative times on all supported days, boundaries, invalid dates, and replacement inputs to the legacy parser, but this is not a formal equivalence proof with upstream.

The results apply only to functions and contracts selected in this fork. They do not prove the upstream commit itself or the crates.io distribution. See the [specification](specification.md) for the selected public wrapper / trait proof surface, and coverage and the latest manifest for its actual status. One forward `From<SystemTime>` refinement is open because native code has panic counterexamples before the Epoch and from year 10000 onward. A bounded body proof does not close this trait refinement. Additional Debug options, private `RawDate` Debug, and dynamic Error payload observers remain unverified.

The proofs use conditional standard-library assumptions listed in the ledger. The scope is 64-bit Linux and the supported date range stated there. Formatter output is guaranteed only under `Ok(()) && append_sink`; arbitrary sinks and partial writes on `Err` are unconstrained. These are not proofs of the Rust standard-library implementation. Application-level date calculations, parser, formatter, and trait bodies are not trusted.

The fork's Cargo.toml adds `creusot-std = "=0.13.0"` and changes the minimum Rust version from 1.56 to 1.91. Dependencies are pinned in the workspace Cargo.lock. No upstream MSRV compatibility is claimed. Formal proof, native tests, and finite upstream differential tests are separate evidence; the latter do not show formal equivalence over all inputs.

`Hash` is a checked implementation that preserves the types and order of the original seven fields. For supported deterministic, non-panicking hashers, it guarantees equal results for equal `HttpDate` values hashed from the same initial internal state. `DefaultHasher::new` is connected as a concrete fixed-key example. No guarantee is made for arbitrary hashers, collision freedom, digest equality across different seeds or Rust versions, or the operation sequence of `hash_slice`. See the specification, assumptions ledger, and latest manifest for details.

The checked implementation of `Error`'s stable trait methods returns `None` from `source` / `cause` and the standard deprecated message from `description`. `From<Error> for io::Error` preserves the `Other` kind and original concrete payload. Under the conditional std model, the body, refinement, and kind-observer harness are proved. Formal guarantees do not cover arbitrary `Into` converters, dynamic `get_ref` / downcast / `into_inner` observers, unstable `provide`, or hidden `type_id`.

The checked Debug implementation explicitly formats the original seven field names and order of public `HttpDate`, and the unit tuple for `Error`. It guarantees exact normal and pretty output for plain flags 0 / 4, with no width / precision / alignment and a space fill, when the result is `Ok` and the sink is an append sink. Pretty-mode numbers are written once by a checked decimal helper, matching the standard `PadAdapter` behavior that omits empty strings. Other format options are passed to the standard builder to preserve native behavior, but their content is not formally guaranteed. Native comparison includes nested formatting and the call sequence of failing writers. See the specification, assumptions ledger, and latest manifest.
