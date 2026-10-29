# Accepted managed macOS run

> Evidence storage: the [committed summary](evidence/summary.json) describes the original accepted inputs. Full logs and repeated snapshots are in the [local archive](evidence/archive.json), not distributed in Git. Packaging has not rerun the full proof pipeline; current verification does not consume historical fixtures.

`default-rbqh8kke` passed on 2026-10-21 for `aarch64-apple-darwin` with CLI preparation patch
`c6f12abf3e1e3b6f2ec910179612f3a71d51351826f7b3c7bdb97e9df700e5eb`
and the current managed runtime identity checks. The immutable local
bundle is [accepted-managed.tar.gz — archived](evidence/archive.json) (`payload/aarch64-apple-darwin-2026-10-21-cli-integration/accepted-managed.tar.gz`),
with hashes in [MANIFEST.json — archived](evidence/archive.json) (`payload/aarch64-apple-darwin-2026-10-21-cli-integration/MANIFEST.json`).
Exact maintained input bytes, locks and frozen shared runner sources are preserved in
[accepted-inputs.tar.gz — archived](evidence/archive.json) (`payload/aarch64-apple-darwin-2026-10-21-cli-integration/accepted-inputs.tar.gz`);
retrieved release source/archive bytes are restored from source.lock.json.

The run passed native debug/release/original-source/doc suites, fresh extraction
against every maintained selected model, a local-package-only clean Lean rebuild,
and a transitive audit of **63 named roots** with **21 API mappings**.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted transitively.
Before/after fingerprints match and include actual Lean/Lake/native and extraction
Rust binary identities, verbose versions and native cfg. Native observations are
finite tests and remain separate from the quantified proofs.

Formal scope: 21 supported table projection/clone callable instances and five private polynomial kernels; no canonical checksum coverage in this profile.

All existing contracts and authored proofs are preserved. Fresh generated files
were copied directly from Aeneas output; their executable Lean matches the
historical models after excluding comments/whitespace. Preparation records raw
and relocated LLBC and checks exact whole-JSON equality except CRC file-name
metadata. Stage2 additionally retains the independently checked type-only GAT
lift, local-display alpha-renaming, standard bitreverse models and all five
negative normalization guards. These frontend/standard-model boundaries are
explicit trust assumptions, not compiler-correctness theorems.

The `x86_64-unknown-linux-gnu` files are candidate copies of native output. No fresh
Linux extraction, native test, Lean build or audit was performed. Historical Linux
success remains tied to the immutable historical evidence and all 88 baseline/228
stage2 input hash bindings. No login, commit, push, recording or publication was
performed by this migration.

The actual pinned CLI prerequisite checks passed for both profiles and stopped at
the expected uncommitted-source gate, before fetch, detached worktree creation or
recording. Logs and configuration identities are preserved inside the local archive
under the original `cli-prerequisites` member path. This does not claim a complete CLI recording.

Earlier accepted input sets are preserved locally under this version’s
`.work/publication-backup/2026-10-22/`, with their original recorded inputs. They
are not distributed by a fresh clone; current archive descriptors describe only
their own inventoried payloads. The current configuration additionally fixes the nested preparation schema and
uses distinct lane-specialized declarations for recorder API mappings.

## Current-input verification (2026-10-23)

Fresh macOS arm64 verification passed using the current source, configuration,
proof packages and regression inputs, without historical evidence inputs. This
run completed the configured native checks and oracles, fresh extraction/model
comparisons, standard Lake build, named theorem/axiom audits and unchanged
before/after fingerprints. It establishes only this profile's stated contracts.

Local-only result: [result.json](/Users/keiichiw/workspace/crate-proofs/.work/current-input-refactor/isolated-checkout/crc/3.4.0/.work/runs/default-7zon60u0/result.json), SHA-256 `d3ac95c9662870263b210c06d7a5ed13f46dc787cbbdaac545a843bde95668b8`.
Input fingerprint: SHA-256 `8b0a1ce2d9bee917273a67e1cc261d1013b827737c5bd75e12b830f2461130d9`. Linux was not run for this result.
