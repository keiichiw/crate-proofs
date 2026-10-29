# Accepted managed macOS run

> Evidence storage: the [committed summary](evidence/summary.json) describes the original accepted inputs. Full logs and repeated snapshots are in the [local archive](evidence/archive.json), not distributed in Git. Packaging has not rerun the full proof pipeline; current verification does not consume historical fixtures.

`stage2-nm6kf18d` passed on 2026-10-21 for `aarch64-apple-darwin` with CLI preparation patch
`c6f12abf3e1e3b6f2ec910179612f3a71d51351826f7b3c7bdb97e9df700e5eb`
and the current managed runtime identity checks. The immutable local
bundle is [accepted-managed.tar.gz — archived](evidence/archive.json) (`payload/aarch64-apple-darwin-2026-10-21-cli-integration/accepted-managed.tar.gz`),
with hashes in [MANIFEST.json — archived](evidence/archive.json) (`payload/aarch64-apple-darwin-2026-10-21-cli-integration/MANIFEST.json`).
Exact maintained input bytes, locks and frozen shared runner sources are preserved in
[accepted-inputs.tar.gz — archived](evidence/archive.json) (`payload/aarch64-apple-darwin-2026-10-21-cli-integration/accepted-inputs.tar.gz`);
retrieved release source/archive bytes are restored from source.lock.json.

The run passed native debug/release/original-source/doc suites, fresh extraction
against every maintained selected model, a local-package-only clean Lean rebuild,
and a transitive audit of **700 named roots** with **75 API mappings**.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted transitively.
Before/after fingerprints match and include actual Lean/Lake/native and extraction
Rust binary identities, verbose versions and native cfg. Native observations are
finite tests and remain separate from the quantified proofs.

Formal scope: 75 additional public mappings, for 96/171 supported built-in callable instances with default. Canonical checksum/update covers Table<0>/Table<1> under the exact recorded parameter, table-coherence and encoded-state preconditions. Sixteen-lane canonical message computation remains excluded.

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

The 700 audited roots comprise all 655 original roots plus 45 exact fixed-lane
word protocol wrappers. Structural checks compare every wrapper binder, result
and direct proof application against the preserved generic contract; the width
conditions, 75 API mappings and combined 96/171 coverage remain unchanged.

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

Local-only result: [result.json](/Users/keiichiw/workspace/crate-proofs/.work/current-input-refactor/isolated-checkout/crc/3.4.0/.work/runs/stage2-ruo3_ag1/result.json), SHA-256 `bd12c3e111a62cc06959bdafa37d5ffb6cea05c05bf03189f9b0a877006c9c25`.
Input fingerprint: SHA-256 `164e5d2fdac8178f5d8a0d75c9c044d9f65eb7032762b1219219a92df9f69b31`. Linux was not run for this result.

## Current-input verification (2026-10-29)

On `aarch64-apple-darwin` (macOS arm64), verification passed with the tracked, unchanged release source under `upstream/` and `cargo-proofs` 0.4.1 based on `344b4797d677636f57ba826dfc6afd22f4c90534` with the concrete API compatibility patch. Native debug, release, upstream and documentation tests passed separately from the formal checks. Fresh extraction and model equality, the Lean build, theorem and axiom audit (700 roots), and unchanged before/after input fingerprints passed. This source, layout and tool migration does not change the contracts or API scope.

The local-only run directory is `.work/runs/stage2-xw_uqhin`. Result SHA-256: `e7d4ab906c609dc1b9bfefcc3072e2ee885e6c1e2583defcd30968f4bc5537af`. Input fingerprint SHA-256: `021c864c2b0b14a80de3a9a441d668f71416f447dd3d52354b577cd87a4c3d58`.

The CLI prerequisite API checks resolved all 75 mappings, but the source gate stopped the CLI before recording. CLI recording and publication were not performed.
