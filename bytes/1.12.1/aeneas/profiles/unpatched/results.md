# Unpatched profile results — 2026-10-25

Status: **passed**, on `aarch64-apple-darwin`.

Command from the repository root:

```sh
bash bytes/1.12.1/scripts/verify.sh --offline
```

Accepted local run: `.work/runs/unpatched-dkrye61t` (relative to the version).
[Summary](evidence/summary-record-ready.json) and [archive descriptor](evidence/archive-record-ready.json)
identify its immutable artifacts. Archive SHA-256: `82a77f18ad3899f3cd53dc699af66cc55fb5bce238d86f8d7f0413bb543ace99`.
Full logs and before/after inputs are in the local content-addressed archive under
`.work/evidence-archives`; they have not been uploaded. Summarization checked every
receipt digest, archive member and matching before/after fingerprint.

## Formal coverage

Five public Take methods: `into_inner`, `get_ref`, `get_mut`, `limit`, `set_limit`.
All five total-success contracts built and passed transitive axiom checks. Only
`propext`, `Classical.choice`, `Quot.sound` are permitted. The generated model was
freshly extracted from the unchanged release and compared byte-for-byte against
the maintained model. Source/tool checks and before/after input fingerprints passed.

Aeneas `be86ab0f1989d04944292b345b24c435be3ad10a` and Charon
`08d7c9d50144bd84848212c24701253585e90d1f` have empty patch lists. The Aeneas Lean
backend and standard library are unchanged. Lean is distribution 4.35.0; extraction
Rust is nightly-2026-09-17. The historical recording CLI preparation patch is still
pinned separately; it is not a compiler/model repair.

The broader extraction was rejected after an invalid recursive Buf declaration
failed Lean checking; see [diagnostic](evidence/broader-extraction-blocker.txt).
No generated code was repaired or partial proof accepted. Other APIs remain
outside this profile. No Linux acceptance is claimed.

## Native observations (not formal proofs)

- Upstream default-feature tests: 1303 passed, including doctests.
- Upstream no-default-feature tests: 1178 passed, including doctests.
- Signed-reader regression: BE/LE/NE at widths 1–7 returned the wrong positive
  value for all-0xff input; width 8 returned -1. Exact residual slices matched.
  [Recorded output](evidence/native-signed-read.txt). Exit 0 means the known
  discrepancy was reproduced; it does not mean the desired signed contract holds.

The Finding was examined during formal-verification work and confirmed by source
review and native reproduction. No Lean counterexample-generation claim follows.
The report links upstream PR #839, merged but not released as of 2026-10-25.

## Historical and publication boundary

The earlier patched profile and its 56 mappings are retained under `default` and
are not evidence for these five contracts. Existing local preview/SARIF records
refer to that historical run. This accepted run is a managed extraction/build/audit,
not a new cargo-proofs SARIF recording. No upload, publication or push occurred.

Primary review checked the five contracts against actual generated bodies, raw
state domains, writeback behavior, commands and coverage mappings. This is not a
new independent review of the historical broad proof.

The accepted run includes the profile-aware `proofs-prepare.toml` configuration.
The earlier unpatched archive/summary are retained separately as intermediate evidence.
