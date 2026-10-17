# adler2 2.0.1 — Aeneas + Lean verification

This independent Cargo workspace prepares unchanged adler2 release sources for
Aeneas/Lean verification, following <https://proofs.rs/book/aeneas>.
See [current results](verification/results.md), [scope](verification/plan.md),
and the [Astra-designed specification](verification/specification.md).
The state-representation contracts cover all checksum bit patterns. The current
objective is optimized update-loop correctness and successful equivalence of
split and concatenated updates. Only the results page identifies the
propositions actually proved in an accepted integrated run.

## Pinned environment

- proofs-rs upstream HEAD checked on 2026-10-16:
  `2f439b8b37dac42e41f8b9dd805ba770d65fc239` (cargo-proofs 0.4.0).
- Registered Aeneas: `be86ab0f1989d04944292b345b24c435be3ad10a`.
- Compatible Charon: `08d7c9d50144bd84848212c24701253585e90d1f`.
- Lean 4.35.0; extraction Rust nightly-2026-09-17; native Rust 1.91.1.
- macOS arm64, OCaml 5.4.0 (`default` opam switch), GNU Make (`gmake`).

A minimal local compatibility patch is applied to this latest proofs-rs commit:
Aeneas makes `name` a reserved token, so the adapter's `let name := ...` audit
fails to parse. The patch renames that local variable to `theorem_name`, without
changing the theorem or axiom checks. Its exact diff is recorded in
`verification/patches/proofs-rs-audit-identifier.patch`; setup reapplies it and
verification checks it. The sibling proofs-rs checkout is unchanged.

The tools are installed in `.tools/` except Rust/Lean toolchains (rustup/elan)
and OCaml packages (opam). Creusot activation is not used. All crate-specific
inputs, generated Lean, scripts, locks and evidence stay in this directory.
`verification/opam-switch.export` records the resolved OCaml packages.

From this directory, in Bash:

```bash
# On a fresh machine: install rustup, elan, opam and GNU Make first.
# Create an OCaml 5.4.0 switch named default, or set AENEAS_OPAM_SWITCH.
bash scripts/setup.sh

# On the prepared machine:
bash scripts/verify.sh
```

Setup restores the recorded revisions; it does not silently upgrade them.
For a future proofs-rs refresh, check upstream HEAD and review the adapter/book,
then update the pin deliberately. The installed CLI is built from the version-local `.tools/proofs-rs/cli`
checkout at that revision plus the recorded compatibility patch.

## Harness layout

- `capture/`: original archive, official sparse registry index and SHA-256 inventory.
- `upstream/`: official Git submodule pinned to
  `89a031a0f42eeff31c70dc598b398cbf31f1680f`, the commit recorded in the release archive.
  The outer Cargo.toml points directly to `upstream/src/lib.rs`; no source copy is built.
  The upstream manifest and source remain unchanged.
- `scripts/check-source.py`: verifies the Gitlink, HEAD, official URL, every tracked
  file's bytes, clean status (including untracked/ignored files), and source identity
  against the checksummed release. It also checks the outer Cargo features and dependencies.
- `tests/harness.rs`: finite reference checks at chunk boundaries and seed cases.
- `proofs/Adler2.lean`: generated local state/optimized-update model; never hand-edit.
- `proofs/Proofs/Smoke.lean`: constructor contract and concrete initial checksum.
- `proofs/Proofs/Codec.lean`: unconditional encode/decode and roundtrip contracts.
- `proofs/Proofs/ChunkLemmas.lean`: exact partition and iterator facts for the pinned slice model.
- `proofs/Proofs/AlgoHelpers.lean`: ordered four-byte widening for the actual lane helper.
- `proofs/Proofs/Spec.lean`, `LaneMath.lean`: independent scalar semantics and lane invariants.
- `proofs/Proofs/AlgoOps.lean`, `LaneLoop.lean`, `Loop4.lean`, `SumLoops.lean`: checked operations and generated-loop contracts.
- `proofs/Proofs/LoopBridge.lean`, `RawBridge.lean`: successful-result and arithmetic bridges.
- `proofs/Proofs/OuterLoop.lean`, `Compute.lean`: arbitrary-length chunk iteration and the complete generated compute body.
- `proofs/Proofs/FinalCombine.lean`, `FinalTail.lean`: exact generated correction and finalization fragments.
- `proofs/Proofs/PublicUpdate.lean`: public update/checksum contracts and successful split/resume laws.
- `verification/theorems.json`: canonical theorem inventory, API mappings and open obligations.
- `proofs/Proofs/Audit.lean`: theorem-kind and transitive axiom audit.
- `proofs/Proofs/RecorderAudit.lean`: adapter-equivalent theorem and axiom checks for mapped APIs.
- `proofs.toml`: public constructor, codec, update and one-shot checksum mappings to their exact contracts.
- `scripts/verify.sh`: fresh extraction, model comparison, separate native tests,
  local Lean rebuild, audit, and before/after input hashes.
- `verification/evidence/`: selected, versioned logs and hash manifests from the
  latest accepted local run. Historical and diagnostic run directories remain
  under ignored `verification/runs/`.

To inspect a newly generated model without replacing the maintained one:

```bash
bash scripts/extract.sh verification/runs/manual
```

Extraction selects local new/from_checksum/checksum/write_slice/adler32_slice
and dependencies under default Cargo features. `crate::` selectors avoid matching
a same-named sysroot dependency. Extracting a function does not prove its contract.
Add APIs explicitly, inspect generated source, write meaningful theorems, and
expand the mapping only after those proofs pass.
The mathematical contracts for state representation and the update algorithm
are defined in verification/specification.md. Sol implements the proofs, with
Astra reviewing the specifications and serving as the proof oracle.

## Restoring the submodule

From the repository root:

```bash
git submodule update --init --recursive -- adler2/2.0.1/upstream
bash adler2/2.0.1/scripts/verify.sh
```

Setup performs the same initialization. Do not use `git submodule update --remote`:
verification requires the pinned commit. Build via the outer Cargo.toml so that
Cargo.lock, build outputs, tests, proofs.toml and Lean sources remain outside upstream.
The submodule commit is recorded both by the parent Gitlink and
`verification/upstream.json`. Matching Git does not alone prove registry identity;
the independent release-source comparison is retained.

## Later cargo-proofs recording

The outer package retains the adapter-compatible location of proofs.toml and
`lean_dir = "proofs"`. The API mapping and the adapter's Lean audit are checked
locally. However, this pinned cargo-proofs version's `git::Worktree::create` does
not initialize submodules in its detached checkout, so a normal recording cannot
currently scan the upstream sources there. Public source links for paths within
a submodule also need review before claiming recorder support.

Recording therefore needs explicit submodule support in proofs-rs first. The
existing audit-variable patch does not add that support. Do not present the local
harness pass as a successful `cargo proofs run`. The CLI also requires the source
commit to be pushed, not only committed; this task does neither. After recorder
support and authorized commit/push, the intended command from `proofs/` remains:

```bash
cargo proofs run --manifest-path ../Cargo.toml -- lake build
```

No recording, login, push, or publication is performed by setup/verify. Local
verification works before committing. Recording checks named Lean theorems; it
does not rerun Charon/Aeneas or prove that a chosen theorem fully specifies Rust.
