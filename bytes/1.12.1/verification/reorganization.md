# Findings report reorganization

## Source and scope

This branch starts from main `5c4e0f729b5bd557451157346250211069968474`
and imports bytes 1.12.1 from develop
`0af93f1c558101bbae5e84dac8bbf95f77794672`.
The develop branch is unchanged. No other crate's development results were imported.

The entire tracked bytes profile is retained, including historical experiments,
source and tool locks, compiler patches, native harnesses, independent specifications,
nine models per target, proof modules, theorem inventory and original evidence
summaries. Historical scripts/localhost URLs are preserved for provenance and are
not current setup instructions. The shared managed runner, its extraction support,
archive utility and regression tests are the only imported runtime infrastructure.

## Initial reorganization report (historical)

[proofs.toml](../aeneas/profiles/default/proofs.toml) is the authoring source.
It explains concrete behavior, preconditions, patched translation boundaries and
excluded APIs. The environment now identifies the accepted managed macOS arm64
run; Linux models alone do not establish Linux acceptance.

One `[[report.findings]]` records the native signed-read discrepancy and associates
`bytes::Buf::try_get_int`, `bytes::Buf::try_get_int_le` and
`bytes::Buf::try_get_int_ne` through `api_paths`. It does not add successful claims
for these APIs. The 56 proof mappings and the complete `[tool]` table are unchanged.
Proof exclusions are kept in limitations rather than duplicated as findings.

Finding API paths require the updated publishing CLI. The preserved pinned CLI is
part of historical verification identity and has not been upgraded. No live API
catalogue resolution, publication dry run, upload or new SARIF was performed.

## Validation and evidence boundary

- Managed layout lint and complete restored source-inventory check passed.
- The historical accepted archive passed integrity checks for all 546 files;
  the archived macOS result records `passed`. This is not a proof replay.
- All imported proof/model/specification/tool-lock/patch files match develop;
  only report/navigation/status prose was rewritten. The tool mappings are equal.
- Shared extraction/source/evidence tests: 40 passed. Managed runner tests: 12
  passed. Read-only tool-cache tests: 20 passed. These are infrastructure tests.
- The native signed-read regression was rerun offline with locked Rust 1.91.1,
  no default features, on aarch64-apple-darwin. All BE/LE/NE width 1–8 checks and
  residual-slice controls reproduced the saved observation. Exit 0 means the
  regression confirmed the discrepancy, not that the desired signed contract holds.

See [structural checks](reorganization/checks.json) and
[native replay](reorganization/native-signed-read.json) for recorded details.
The independent specification, proof implementation and prior oracle reviews are
retained; this reorganization reviews their correspondence and report claims without
claiming a new independent proof review.

The full extraction, Lean build and transitive axiom audit were **not rerun**.
Editorial changes affect the managed input fingerprint, so prior acceptance remains
tied to its original archived inputs. A fresh full run and a compatible recorder
are required before asserting acceptance of this checkout or publishing a new run.


## Subsequent unpatched profile (2026-10-25)

The initial reorganization above preserved the patched profile. The active default
is now `unpatched`, with five Take structural contracts and a separately reproduced
native Finding. See [current results](../aeneas/profiles/unpatched/results.md) and
[specification](../aeneas/profiles/unpatched/specification.md). No earlier 56-claim
SARIF or acceptance record establishes coverage of the new profile. Historical
source/model/proof/patch files under `profiles/default` remain unchanged.
