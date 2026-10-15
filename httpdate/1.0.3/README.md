# Verification of httpdate 1.0.3

This is a verification fork of `httpdate` 1.0.3. Its source and changes are recorded in [provenance](verification/upstream.md), its contracts in the [specification](verification/specification.md), and its proved scope in [coverage](verification/coverage.md). See [verification method](verification/trial/method.md) for the approach used in the trial.

- `crate/`: upstream-derived code, licenses, tests, and Creusot contracts
- `verification/`: specification, provenance, results, and evidence
- `verification/trial/`: probes, independent models, upstream source for comparison, and trial results used to investigate missing support
- `scripts/`: verification and result-checking scripts for this version
- `.agents/skills/httpdate-verification/`: the httpdate-specific skill

This directory is an independent Cargo workspace. Prepare the common tools using the [top-level instructions](../../README.md); `why3find.json` refers to the common configuration.

Run from the repository root:

```bash
bash httpdate/1.0.3/scripts/verify.sh
```

To run only native tests:

```bash
source scripts/activate.sh
cargo test --locked --release --manifest-path httpdate/1.0.3/Cargo.toml -p httpdate
```

The verification checks the shared byte / calendar core and selected public wrapper and trait bodies under stated conditions. The raw parser returns permissive `RawDate` values; only after calendar validation does it construct a flat seven-field `HttpDate` with a checked invariant. The selected surface includes `FromStr` / `parse_http_date`, bounded `fmt_http_date` and `Display`, `Eq` / `Ord` / `PartialOrd` / `Clone`, and some time conversions. `Eq` uses the original seven fields; `Ord` uses shared integer-second comparison. One forward `From<SystemTime>` refinement remains open because the original implementation panics before the Epoch and in year 10000. Normal and pretty Debug output is verified under plain options and a faithful append-sink condition.

Public-wrapper proofs depend on the standard-library boundary specifications listed in the [assumptions ledger](verification/stdlib-assumptions.md), and are limited to 64-bit Linux or macOS arm64 and the stated date range. Formatter content is guaranteed only when the result is `Ok(())` and the sink is a faithful `append_sink`; arbitrary sinks and partial writes on failure are not specified. The standard-library implementation itself is outside the proof scope. See coverage and the latest manifest for each function's preconditions, guarantees, open / unverified areas, and current evidence. Do not claim overall success or a fixed goal count before a full run completes for the current proof harness and source. Native differential tests show observed agreement on the compared inputs; they are not a formal equivalence proof with upstream.

The verification script writes Coma and proof.json into a new `verif/httpdate-run-*/`. It updates `verification/evidence/latest/` only after checking native tests, all target VCs and supporting conditions, and before / after fingerprints of inputs and tools. Evidence records SHA-256 hashes of sources, contracts, configuration, Cargo.lock, scripts, selected tool executables, their versions, and the run log.

To rerun the independent boundary models:

```bash
bash httpdate/1.0.3/verification/trial/boundary-model/run.sh
bash httpdate/1.0.3/verification/trial/trait-models/run.sh
```

The first is an independent experiment limited to 64-bit Linux or macOS arm64 that informed the standard-library boundary model used in production. The second is an abstract three-field Eq / Ord experiment that differs from the real type. Proofs from the first experiment are not public API proofs. `trial/probes/run.sh` and `trial/trait-probes/run.sh` reproduce investigations that include unresolved conditions and save their results separately.

`crate/proofs.toml` is configuration for a later cargo-proofs recording. Local proofs for public wrappers have also been added, but they have not been registered in the public API catalogue. The saved evidence consists of local Creusot results; no SARIF or proofs.rs registration has been made.

The provenance of the crates.io distribution and the upstream-to-fork changes are summarized in the [correspondence table](verification/correspondence/README.md). The independent native comparison of public APIs can be rerun with `bash httpdate/1.0.3/scripts/check-correspondence.sh`, using ordinary Rust/Cargo without the formal verification environment. It saves a native-only result; `capture-correspondence.py --bind RUN_DIRECTORY` separately binds it to matching formal evidence. See the correspondence guide for prerequisites and commands. The identity of the distribution and source-copy runtime code, and the fork comparison results, are recorded separately; none is treated as a formal equivalence proof.

The parse/format-focused report is maintained in [crate/proofs.toml](crate/proofs.toml). Follow the [submission guide](verification/proofs-rs-report-review.md) for its isolated recorder, local source-span checks, and separate SARIF recording. Registration still requires a public source commit and authoritative API-catalogue matching.

`Hash` is a checked implementation that preserves the types and order of the original seven fields. For supported deterministic, non-panicking hashers, it guarantees equal results for equal `HttpDate` values hashed from the same initial internal state. `DefaultHasher::new` is connected as a concrete fixed-key example. No guarantee is made for arbitrary hashers, collision freedom, digest equality across different seeds or Rust versions, or the operation sequence of `hash_slice`. See the specification, assumptions ledger, and latest manifest for details.

The checked implementation of `Error`'s stable trait methods returns `None` from `source` / `cause` and the standard deprecated message from `description`. `From<Error> for io::Error` preserves the `Other` kind and original concrete payload. Under the conditional std model, the body, refinement, and kind-observer harness are proved. Formal guarantees do not cover arbitrary `Into` converters, dynamic `get_ref` / downcast / `into_inner` observers, unstable `provide`, or hidden `type_id`.

The checked Debug implementation explicitly formats the original seven field names and order of public `HttpDate`, and the unit tuple for `Error`. It guarantees exact normal and pretty output for plain flags 0 / 4, with no width / precision / alignment and a space fill, when the result is `Ok` and the sink is an append sink. Pretty-mode numbers are written once by a checked decimal helper, matching the standard `PadAdapter` behavior that omits empty strings. Other format options are passed to the standard builder to preserve native behavior, but their content is not formally guaranteed. Native comparison includes nested formatting and the call sequence of failing writers. See the specification, assumptions ledger, and latest manifest.
