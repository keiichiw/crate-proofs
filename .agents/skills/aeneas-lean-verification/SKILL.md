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

Read [setup and runner](references/setup-and-runner.md) when preparing a target or
changing its toolchain. Read the target's specification and current results before
extending its scope. Use [proof patterns](references/proof-patterns.md) for loops,
modular arithmetic, model boundaries, and stateful API composition.

1. Establish source identity. Prefer an unchanged upstream submodule plus an external
   manifest pointing at its source. Pin the Gitlink and verify the actual checkout,
   every tracked file's bytes and clean status. Compare release source separately
   against the checksummed registry archive; a Git pin alone does not prove release
   identity. Keep the outer manifest's semantic build surface consistent with upstream.
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

## Shared commands

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

The completed [adler2 example](../../../adler2/2.0.1/README.md) illustrates the layout;
its [results](../../../adler2/2.0.1/verification/results.md) distinguish formal scope,
native observations, trusted models, and recorder limitations. Reuse patterns, not
its crate-specific contracts, bounds or API list. Paths from this skill to repository
root use `../../..`.
