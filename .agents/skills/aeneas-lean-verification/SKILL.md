---
name: aeneas-lean-verification
description: Verify Rust crate implementations with Aeneas and Lean, using pinned extraction, total-success functional contracts, theorem audits, and reproducible local evidence. Use when setting up or extending an Aeneas/Lean crate proof.
---

# Aeneas + Lean verification

Keep target-specific sources, pins, specifications, configuration, scripts and evidence
under `<crate>/<version>/`, with an independent Cargo workspace. Use the version's
AGENTS.md and environment. Do not activate the repository's Creusot environment for
Aeneas. This skill supplies a workflow, not an automatic algorithm prover.

## Start or restore a target

For a new crate, follow the [new-crate procedure](../../../verification/templates/aeneas-managed/README.md). It is the primary setup path; the reference below supplies extractor/auditor details. Migrated Aeneas workspaces use managed profiles; unmigrated targets retain their own instructions. Recorded acceptance remains tied to original input fingerprints.

Read [setup and runner](references/setup-and-runner.md) when preparing a target or
changing its toolchain. Read the target's specification and current results before
extending its scope. Use [proof patterns](references/proof-patterns.md) for loops,
modular arithmetic, model boundaries, and stateful API composition.
When extraction or generated Lean fails, use [boundary diagnosis](references/boundary-diagnosis.md)
to locate the failing stage and design a faithful minimal reproduction. For experiments
whose failures or interruptions must remain analyzable, use the optional
[trial recorder](../../../verification/trial-recording.md).

1. Establish source identity. For managed targets, pin the crates.io archive and full
   file inventory in source.lock.json and restore unchanged source into ignored
   .work/source. Use full-commit Git retrieval only for unreleased sources. Keep the
   outer manifest's semantic build surface consistent with the release. Existing
   unmigrated submodules retain their recorded Gitlink/clean-byte/release checks;
   migration is explicit, never an implicit change during verification.
2. Pin proofs-rs, Aeneas, compatible Charon, extraction Rust, native Rust and Lean.
   For an explicit latest-version request, resolve upstream now and record the date
   and commit; the previous target's pins are a restoration baseline, not latest.
   Record compatibility patches exactly and check them. Never silently upgrade tools
   or dependency locks while reproducing evidence.
3. Extract local `crate::...` entries into a fresh directory using the shared
   `scripts/aeneas-extract.py`. Configure expected generated files and required
   definitions in the version-local `verification/aeneas.json`. Inspect dependency
   bodies and source spans. Never hand-edit generated Lean, accept partial output
   with application axioms, or replace the implementation with a convenient model.
4. Define an independent mathematical specification and observables first. Prefer
   total-success contracts `∃ out, actualFunction input = Result.ok out ∧ property out`.
   Include valid raw constructor states, empty inputs, errors where applicable, and
   actual representation bounds. Do not assume implementation correctness or weaken
   public contracts to make private arithmetic lemmas fit. Respect the user's model
   roles if delegation is requested; otherwise do not require specific agents.
5. Prove the actual generated bodies. Build one useful core before claiming broader
   coverage. Keep incomplete experiments in ignored run directories, outside the
   maintained proof tree. For proof abstractions of monadic fragments, prove exact
   equality to the generated fragment as part of the dependency chain.
6. Record audited theorem names/modules in `verification/theorems.json`. Map actual
   public contracts in `proofs.toml`; keep helper/model/loop lemmas separate from API
   coverage. Use shared `scripts/aeneas-audit.py` with `--proofs-toml` to check mappings,
   theorem kind and transitive dependencies. Only `propext`, `Classical.choice` and
   `Quot.sound` are permitted; no `sorryAx`, custom axiom or native-decision axiom.
7. Integrate the helpers in a version-local verifier. Regenerate and compare all
   maintained model files, clean only the local Lake package, rebuild/audit, run native
   tests separately, and compare input fingerprints before/after. Include the shared
   scripts themselves in the fingerprint. Preserve historical runs. Report scope,
   source/model trust and excluded APIs in results; neither extraction nor a build
   alone proves a contract.

## Managed targets

Use the version-local setup.sh and verify.sh wrappers for targets with
`aeneas/profiles.toml`. The [management guide](../../../verification/aeneas-management.md)
describes source/tool locks, profile layout, per-target generated Lean, shared
ignored tool caches, and the SARIF boundary. Setup logs and repository scripts must
not be embedded in SARIF. Formal recording still runs standard Lake and CLI audits.
Do not claim a draft profile is migrated until fresh verification passes.

## Shared commands (legacy/custom runners)

Run from the repository root in Bash. Replace `<crate>/<version>` with the prepared
target; the source/tool checks described below belong in its surrounding verifier:

```bash
VERSION_ROOT="$PWD/<crate>/<version>"
source "$VERSION_ROOT/scripts/env.sh"
mkdir -p "$VERSION_ROOT/verification/runs"
RUN="$(mktemp -d "$VERSION_ROOT/verification/runs/check-XXXXXXXX")"
python3 scripts/aeneas-extract.py "$VERSION_ROOT" \
  --config "$VERSION_ROOT/verification/aeneas.json" --output "$RUN/generated"
python3 scripts/aeneas-audit.py "$VERSION_ROOT" \
  --inventory "$VERSION_ROOT/verification/theorems.json" \
  --proofs-toml "$VERSION_ROOT/proofs.toml" --output "$RUN/audit"
```

Both output directories must be new. These commands do not install tools, validate
upstream source identity, prove Rust-to-Lean translation, or publish a proofs.rs report.
See the reference for configuration and the surrounding runner responsibilities.

Use the managed template for new targets and each migrated version's README and
profile results for concrete examples. Reuse patterns, not another crate's contracts,
bounds, API list or acceptance claims. Paths from this skill to repository root use
`../../..`.
