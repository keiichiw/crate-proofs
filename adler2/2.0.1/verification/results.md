# Local formal verification results

Checked on 2026-10-16, macOS arm64. Optimized computation core and split/resume correctness passed.
Astra designed and reviewed the contracts; Sol implemented and executed the Lean proofs,
consulting Astra as the oracle. The primary reviewed source identity, scope and evidence.
The optimized Adler-32 update algorithm is proved in the extracted model.
This is not a whole-crate or Rust-to-Lean translation-correctness proof.

## Proven scope

The [canonical inventory](theorems.json) contains 46 audited root theorems and
five public API mappings. Audits traverse proof dependencies, including private
lemmas; the root count is not a count of public APIs or all auxiliary theorems.

- `compute_spec` proves the actual generated optimized compute body succeeds and
  returns exactly the normalized scalar fold, for every `Adler32` state and
  every representable input slice. No normalized-seed or artificial length
  restriction is imposed. All loops, machine arithmetic and indices are covered
  by total-success proofs; private safety conditions are discharged internally.
- `write_slice_spec` transfers that contract to the public update function.
  `adler32_slice_spec` proves the one-shot checksum equals the encoding of the
  scalar fold from `(1, 0)`.
- `split_update_spec` and `write_slice_append_spec` prove both split and one-shot
  updates succeed with exactly the same complete state. They take slices `xs`,
  `ys` and `whole` satisfying `whole.val = xs.val ++ ys.val`; this makes combined
  slice representability explicit without bounding either input artificially.
- `write_slice_resume_spec` proves the same result after saving the intermediate
  checksum, restoring it with `from_checksum`, and continuing. The supplementary
  `resume_checksum_spec` handles every arbitrary U32 seed directly.
- Constructor, exact checksum encoding/decoding, and both state roundtrips are
  preserved from the previous milestone. Empty updates normalize raw seed halves,
  including `(65535, 65535)` to `(14, 14)`.
- Actual lane helpers, every generated loop and final correction/cast fragments
  are connected to the actual compute body by checked equalities. Chunk and
  iterator lemmas concern the pinned standard-library model; equivalence of that
  library model to Rust remains a trusted boundary.

The [Astra specification](specification.md) records the contracts and invariants.
`proofs.toml` maps `new`, `checksum`, `from_checksum`, `write_slice` and
`adler32_slice` to their contracts. Split/resume and helper lemmas are audited
supplementary evidence. No selected computation-core obligation remains open;
the excluded APIs below are not covered by that statement.

## Accepted run

- Latest proofs-rs upstream base: `2f439b8b37dac42e41f8b9dd805ba770d65fc239`,
  cargo-proofs 0.4.0, with the recorded local audit-identifier compatibility patch.
- Pinned Aeneas/Charon built; Lean 4.35.0 and the official pinned Lake dependency resolved.
- Official upstream submodule at `89a031a0f42eeff31c70dc598b398cbf31f1680f`:
  Gitlink, HEAD, URL, every tracked file's bytes and clean status checked before/after.
- Release checksum and upstream src/ identity with the captured release: passed.
- Outer Cargo identity, features and dependencies match the upstream manifest;
  compilation/extraction reads `upstream/src/lib.rs` directly.
- Local `crate::` extraction includes actual optimized compute, all its loops,
  write_slice and adler32_slice without a same-named sysroot copy or axiomatized bodies.
  Their functional contracts now pass against the unchanged generated bodies.
- Fresh Charon/Aeneas extraction matches `proofs/Adler2.lean` byte-for-byte.
- All 46 inventory root theorems: passed after cleaning and rebuilding local Lean targets.
- Transitive audit: only `propext`, `Classical.choice`, `Quot.sound`.
- Adapter-equivalent checks for all five mapped API theorems: passed.
- Every Lake dependency checkout matches its lockfile revision and has no tracked
  source changes or nonignored untracked files, checked before and after.
- Native default features: 6 upstream unit tests, 2 harness tests, 4 doctests passed.
- Native no_std configuration: 5 upstream unit tests, 2 harness tests, 3 doctests passed.
  These are native finite observations, not formal no_std proofs.
- Before/after input and executable fingerprints match; local Lean package outputs were cleaned.
Fresh local run: [result](evidence/check-mxgcyMMw/result.json),
[complete log](evidence/check-mxgcyMMw/run.log),
[generated Lean model](evidence/check-mxgcyMMw/generated/Adler2.lean),
[Lean theorem audit](evidence/check-mxgcyMMw/lean-audit.log),
[adapter-equivalent audit](evidence/check-mxgcyMMw/recorder-audit.log),
[default-feature native tests](evidence/check-mxgcyMMw/native-default.log),
and [no_std native tests](evidence/check-mxgcyMMw/native-no-std.log).
The [evidence manifest](evidence/check-mxgcyMMw/manifest.json) hashes all 11 copied
run files, including both input fingerprints and the fresh Charon LLBC output.
The [saved-evidence checker](evidence/check-evidence.py) validates this package
against the maintained model and theorem inventory without reading ignored runs.
Result SHA-256: `92fcd82a153a83f17357055e81061320c4ca23dd9dda354a99d6b17c23a48f53`.
The original run remains at ignored `verification/runs/check-mxgcyMMw/`.

The upstream unpatched audit failed with `ill-formed syntax` at `let name` after
importing Aeneas (which reserves that token). The version-local patch changes
only that variable's name. The sibling proofs-rs repository is untouched.

The setup script assembles the individually exercised installation commands;
restoration on a separate fresh machine has not been tested. Charon's upstream
`make setup-charon` also attempted documentation generation without odoc;
setup.sh builds the required Rust binaries directly and builds Aeneas separately.

`cargo proofs run` was not executed. The pinned CLI does not initialize Git
submodules in its detached checkout, so recording this layout requires additional
recorder support (and review of submodule source links). The Lean adapter audit
passes locally, which does not establish a complete recorded report.
The CLI also requires committed and pushed source. No login, commit, push,
publish or publish --dry-run was performed. Submodule registration staged only
.gitmodules and the upstream Gitlink; other task changes remain unstaged.

Earlier copy-layout, submodule-bootstrap, and state/prerequisite results remain
unchanged in ignored `verification/runs/`; they do not establish freshness or
update correctness for this accepted run. Earlier source-guard and adapter unit
diagnostics also remain there, but were not rerun or packaged as part of this
fresh integrated verification. Failed or partial probes are not accepted evidence.

## Excluded scope and trust

Generic BufRead IO and its error behavior, derived traits and Hasher laws,
no_std formal verification, alternative targets and whole-crate correctness
remain outside the proven scope. Default-feature macOS arm64 extraction is the
selected target. Charon/Aeneas translation, pinned standard-library semantics,
and the Lean kernel are trusted; the transitive proof audit permits only
`propext`, `Classical.choice`, and `Quot.sound`. No sorry, native-decision axiom,
custom axiom or assumed implementation-correctness parameter is accepted.
See [the plan](plan.md).
