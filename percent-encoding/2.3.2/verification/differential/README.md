# Native percent-encoding differential harness

This standalone workspace compares the verification fork at `../../crate` with a staged copy of the immutable registry capture at `upstream-copy`. Cargo cannot write two packages with the same name and version to one lockfile, so the staged copy changes only `[package].name` in its normalized `Cargo.toml` to `percent-encoding-upstream`; all source files are copied from `../../capture/source`, which remains untouched. It checks observable behavior over all 256 one-byte inputs and all 65,536 two-byte inputs, fixed-seed byte strings, and targeted malformed/valid percent escapes and UTF-8 cases.

Run the complete native suite from the repository root using ordinary Rust 1.91.0/Cargo, a linker, Bash, and Python 3. Formal tools and activation are not required:

```sh
bash percent-encoding/2.3.2/verification/differential/run-full-scope.sh
```

Missing locked dependencies may be downloaded; set `CARGO_NET_OFFLINE=true` to require a populated cache. The runner preserves the caller’s Cargo/Rustup homes and honors `CARGO_TARGET_DIR`. Its differential log contains one JSON summary line. Any mismatch panics and exits nonzero. The upstream crate's unit tests remain separate and can be run with `cargo test --offline --all-features --manifest-path percent-encoding/2.3.2/verification/differential/upstream-copy/Cargo.toml`.

This is finite native differential evidence for the exercised APIs and inputs. It is not a blanket source-equivalence claim or a formal proof.

## Frozen native run

At the core agent's declared source freeze, the offline harness passed. The JSON line in [differential-run.log](differential-run.log) records 65,945 input strings: 256 single bytes, all 65,536 two-byte sequences, 129 xorshift-generated inputs using seed `0x9e37_79b9`, and 24 targeted percent-escape/UTF-8 strings. Each input was encoded against seven sets (empty, controls, non-alphanumeric, and four custom sets) and decoded. It also compared 892,191 encoder chunks and 139,659 decoded output bytes, iterator size hints and clone suffixes, Cow contents/borrowing, strict UTF-8 errors, lossy UTF-8, wrappers, all 256 `percent_encode_byte` results, set observations, and four high-byte panic outcomes.

The runner performed these additional offline checks from the repository root after sourcing `scripts/activate.sh`:

```sh
CARGO_TARGET_DIR=/workspace/proof-env/percent-encoding/2.3.2/verification/differential/target-fork-native cargo test --offline --all-features --manifest-path percent-encoding/2.3.2/crate/Cargo.toml
CARGO_TARGET_DIR=/workspace/proof-env/percent-encoding/2.3.2/verification/differential/target-fork-native cargo test --offline --doc --all-features --manifest-path percent-encoding/2.3.2/crate/Cargo.toml
CARGO_TARGET_DIR=/workspace/proof-env/percent-encoding/2.3.2/verification/differential/target-fork-native cargo check --offline --manifest-path percent-encoding/2.3.2/crate/Cargo.toml
CARGO_TARGET_DIR=/workspace/proof-env/percent-encoding/2.3.2/verification/differential/target-fork-native cargo check --offline --no-default-features --manifest-path percent-encoding/2.3.2/crate/Cargo.toml
CARGO_TARGET_DIR=/workspace/proof-env/percent-encoding/2.3.2/verification/differential/target-fork-native cargo check --offline --no-default-features --features alloc --manifest-path percent-encoding/2.3.2/crate/Cargo.toml
CARGO_TARGET_DIR=/workspace/proof-env/percent-encoding/2.3.2/verification/differential/target-upstream-unit cargo test --offline --all-features --manifest-path percent-encoding/2.3.2/verification/differential/upstream-copy/Cargo.toml
```

All passed. Fork and staged-upstream unit runs each passed 18 tests and six doctests; the fork's standalone doctest run passed six. The corresponding outputs are in `fork-unit-all-features.log`, `fork-doc-all-features.log`, `fork-check-default.log`, `fork-check-bare.log`, `fork-check-alloc.log`, and `upstream-unit-all-features.log`. `cargo-check.log` records the clean initial compile. The earlier `initial-cargo-check.log` preserves Cargo's lockfile collision diagnostic that led to the documented staged-copy manifest rename.

## Phase 2 native rerun

After the phase 2 source freeze, the same offline native differential harness and fork/upstream checks were rerun against the latest crate. All passed. The JSON summary in `differential-run-phase2.log` matches the earlier input and observation counts: 65,945 input strings, 461,615 encoding cases, 65,945 decode cases, and 20 other category counters including all 256 `percent_encode_byte` values and four high-byte panic comparisons. Fork unit tests passed 18 tests and six doctests; the separate fork doctest run passed six, and the staged upstream unit command passed 18 tests and six doctests. Default, no-default-features, and alloc-only checks all passed. Exact outputs are in the `*-phase2.log` files alongside this README. This remains finite native differential evidence over the listed APIs and corpus, not a blanket source-equivalence claim or formal proof.

## Full-scope rerun after UTF-8 integration

`run-full-scope.sh` is the standalone native runner for the integrated UTF-8 helpers. Each invocation creates a UTC/PID `RUN_ID`, puts it in all seven logs and the fingerprint file, and passes it to the harness JSON summary through `PERCENT_ENCODING_RUN_ID`. It writes `differential-run-full-scope.log`, `fork-unit-all-features-full-scope.log`, `fork-doc-all-features-full-scope.log`, `fork-check-default-full-scope.log`, `fork-check-bare-full-scope.log`, `fork-check-alloc-full-scope.log`, and `upstream-unit-all-features-full-scope.log`. Before binding these logs to formal evidence, freeze the inputs and require matching fingerprints.

The final full-scope run completed against the core agent's frozen runtime with matching before/after fingerprints. Its run ID is `percent-encoding-2.3.2-full-scope-20261014T030934Z-119616`; the 30 sorted SHA-256 rows in `source-fingerprint-full-scope.txt` match exactly in both sections. The same ID appears in every log and in the JSON summary.

The harness passed for 65,945 input strings: 256 single-byte values, all 65,536 two-byte sequences, 129 deterministic xorshift inputs (seed `0x9e37_79b9`), and 24 targeted malformed/valid percent and UTF-8 cases. Across seven encode sets it checked 461,615 encoding cases, 892,191 chunks, 1,815,421 size-hint observations, 892,191 partial clone states, and 1,784,382 equality checks. Decode coverage included 65,945 cases, 139,659 output bytes, 271,549 size-hint observations, 139,659 clone states, 205,604 Cow observations, and 411,208 strict/lossy UTF-8 result checks. The run also checked six forced-owned invalid UTF-8 error values, 256 `percent_encode_byte` values, seven AsciiSet operation cases, four high-byte panic comparisons, 129,213 UTF-8 wrapper cases, 18,459 decode-str wrapper cases, 3,118,834 Debug text comparisons, three single-escape Cow cases, six failing Display cases with 21 writes, and 374 failing Debug sink cases with 8,667 writes.

Fork all-feature tests passed 18 unit tests and six doctests; the separate doctest run passed six. Staged-upstream all-feature tests passed 18 unit tests and six doctests. Fork default, no-default-features, and alloc-only checks all passed. Exact outputs are in `differential-run-full-scope.log`, `fork-unit-all-features-full-scope.log`, `fork-doc-all-features-full-scope.log`, `fork-check-default-full-scope.log`, `fork-check-bare-full-scope.log`, `fork-check-alloc-full-scope.log`, `upstream-unit-all-features-full-scope.log`, and `source-fingerprint-full-scope.txt`.

This records finite native correspondence for the exercised APIs and corpus. It is not a blanket source-equivalence claim or a formal proof.
