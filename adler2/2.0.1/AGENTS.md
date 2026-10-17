# adler2 2.0.1 — Aeneas / Lean

- This version uses Aeneas, not Creusot. Use `scripts/env.sh`; do not source the root Creusot activation.
- Keep `upstream/` at the pinned Git submodule commit, completely clean. Do not edit files inside it. The outer manifest compiles `upstream/src/lib.rs` directly; keep features/dependencies identical to upstream and source bytes identical to `capture/source/src`. Run `scripts/check-source.py`.
- See `README.md` and `verification/plan.md` for commands and scope. Tool pins are in `verification/toolchain.json`.
- Generate Lean from actual Rust with pinned Charon/Aeneas. Do not hand-edit generated models or replace algorithm bodies with axioms.
- A successful build is not an algorithm proof. Distinguish proved state-representation laws, private helper and standard-model lemmas, native observations, extraction, proved update-core contracts, and excluded APIs. verification/theorems.json is the audited theorem inventory; verification/results.md records the accepted run.
- Do not add `sorry`, custom axioms, or application assumptions. Audit named theorems transitively.
- Use default Cargo features for proofs.rs compatibility. no_std native testing is separate evidence.
- `cargo proofs run` needs submodule support in the current CLI and committed/pushed inputs; publication and push need explicit user authorization. Do not run publish, including --dry-run, for setup.
