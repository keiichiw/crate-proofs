# Verification milestones

Target: adler2 2.0.1. The official sparse registry index selects this latest stable
release on 2026-10-16. `capture/manifest.json` records the archive checksum and
source inventory. The crates.io version API returned HTTP 403, so provenance
uses the unmodified official sparse-index response. VCS metadata in the release
is a separate identity; the pinned submodule commit matches that VCS metadata. Every tracked submodule file is checked against Git and its src/ inventory is checked against the release. The whole Git tree is not claimed to equal the normalized Cargo release archive.

The implementation under `upstream/src/` is a clean, pinned upstream submodule. The external Cargo.toml references it directly and provides an independent workspace and native integration harness; its features, dependencies and package identity are checked against upstream. Default feature `std` is used for
extraction to match the current proofs.rs adapter. Host: macOS arm64. Normal
runtime dependencies: none; optional rustc-std-workspace-core is unselected.
There is no build script, unsafe code, FFI, or async behavior in the selected core.

## Selected and open scope

- Extract: `Adler32::new`, `Adler32::from_checksum`, `Adler32::checksum`,
  `Adler32::write_slice`, `adler32_slice`, and their dependency closure, including
  optimized `algo::Adler32::compute` and lane helpers. Use Charon `crate::...`
  starting paths and the Aeneas preset to select the local crate unambiguously.
- Bootstrap theorem: `new` succeeds with exactly `{a=1,b=0}`; no input precondition.
- Auxiliary theorem: checksum of that concrete initial state equals 1.
- State-representation obligations: exact arithmetic encoding of every Adler32,
  exact low/high-half decoding of every U32, and both monadic roundtrips.
  These are unconditional total-success theorems, including non-normalized seeds.
- Update obligations: `write_slice`, `compute`, and `adler32_slice` total success
  and agreement with the normalized scalar fold, for arbitrary states and slices.
  Prove actual split-update equivalence: any representable concatenation and its
  two successive updates both succeed with the same complete state. Also establish
  resumption after serializing the intermediate checksum and decoding it back.
  These public contracts have no normalized-seed or artificial input-length
  hypothesis; private loop bounds must be discharged by the enclosing proof.
- Independent scalar specification laws do not prove the Rust update functions.
  See [the Astra-designed specification](specification.md) for exact statements.
  [Results](results.md) owns proof status and remaining obligations.
- Excluded: generic `BufRead` IO/error behavior, derived Debug/Clone/Copy, Hasher
  laws/default methods, rustc-dep-of-std, alternative targets and no_std proofs.

Specify Adler-32 as the fold of
`a'=(a+byte)%65521`, `b'=(b+a')%65521`, then prove correspondence with the
four-lane optimized loop, overflow bounds, and concatenation/resumption.
`from_checksum` accepts arbitrary u32, including halves >=65521; never silently
assume every public constructor produces normalized components. Empty updates
normalize these halves in the release implementation.

## Trust and evidence

Charon/Aeneas extraction and standard-library models are trusted translation
boundaries, not checked Rust/Lean equivalence. The Lean kernel checks the named
proofs; the audit permits only propext, Classical.choice, Quot.sound. No custom
axioms or sorry are accepted. The generated model selects the local `adler2.Adler32`, with source span
`upstream/src/lib.rs`. Bare `adler2::...` starting paths also selected a sysroot
copy in an investigation; `crate::...` avoids it. Partial generated files with
axiomatized bodies are diagnostic artifacts, not accepted verification inputs.

The native harness checks published vectors, seed roundtrips, empty inputs,
4-byte and 22208-byte chunk boundaries, and incremental updates against a u64
scalar reference. These finite observations are not formal algorithm proofs.

`scripts/verify.sh` regenerates the model in a fresh directory, compares it with
the maintained generated source, cleans local Lean targets, builds and audits
named theorems, and checks input freshness. Results go in `verification/runs`.
Status belongs in `verification/results.md`, outside the input fingerprint.

The environment milestone established the toolchain and bootstrap harness.
The current objective is functional correctness of the optimized update loop and
actual API concatenation/resumption, building on the state-representation contracts. Astra designs and reviews
specifications; Sol implements and executes the proofs, consulting Astra as an
oracle. The primary reviews source correspondence, commands, evidence and scope.
Do not weaken contracts or replace the upstream implementation to close a goal.
`cargo proofs run` is currently blocked by the pinned CLI not initializing submodules in its detached checkout. Future recording also requires committed and pushed source; do not log in,
push, or publish (including publish --dry-run) as part of setup.

The latest upstream CLI requires the recorded audit identifier compatibility
patch for this Aeneas version. It changes only the Lean local variable name,
not the allowed axioms or theorem checks. RecorderAudit.lean tests the resulting
adapter-equivalent checks against the mapped proof modules. The canonical theorem inventory drives both audits and run results.
