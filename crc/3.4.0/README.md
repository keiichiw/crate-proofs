# crc 3.4.0

The managed Aeneas profiles preserve the existing mathematical contracts and use
unchanged crates.io source tracked in `upstream/` and checked against
`source.lock.json`. Each version has its own Cargo workspace and lockfile.
The original MIT and Apache-2.0 license texts are included both in `upstream/`
and beside this file; `NOTICE` identifies the release and the generated Lean
material derived from it.

```bash
bash crc/3.4.0/scripts/setup.sh
bash crc/3.4.0/scripts/verify.sh --offline
bash crc/3.4.0/scripts/verify.sh --profile stage2 --offline
```

`default` proves 21 supported table projection/clone callable instances and five
private polynomial kernels. `stage2` adds 75 public contracts, including canonical
checksum and incremental update for Table<0>/Table<1>, for a combined 96 of the
171 supported built-in callable instances. Preconditions on parameters, coherent
cached tables and incoming encoded state remain explicit. The sixteen-lane
canonical message algorithm remains outside formal coverage. Native tests are
finite independent-oracle observations, separate from quantified Lean proofs.

Stage2 checks each lane-specialized word protocol wrapper against its current
generic theorem, including binders, width bounds, result and lane application.
The current inventory and API mapping are checked for completeness and uniqueness;
no previous root count or input map is an acceptance condition.

Profiles live under `aeneas/profiles/{default,stage2}`. Each profile contains its
specification, theorem inventory, API report, exact source/tool locks, adapters,
per-target generated Lean and evidence. The stage2 Lake dependency is the managed
default profile. Current platform acceptance is recorded in each `results.md`;
Linux candidates are not evidence of a fresh Linux verification run.

Extraction preserves the existing type-only GAT lift, exact display-name
alpha-renaming checker, standard bitreverse boundary and all five negative
normalization guards. A separate preparation step relocates only CRC file-name
metadata to `crc-source/<release-path>` for portable source comments. Each run
retains the immutable original LLBC, relocated LLBC, raw/relocated hashes and a
checked inverse equality of the complete JSON tree; declaration bodies, types,
spans, file contents, IDs and operations remain identical. This preparation
transformation is not a compiler-correctness proof. Generated Lean is copied
unchanged from Aeneas output and compared byte for byte during verification.

Original accepted bundles remain in the local-only archives identified by each
profile's `evidence/archive.json`. Verification does not read them. It checks the
current source lock, catalog, extraction configurations, generated Lean and proof
inventory directly. Earlier acceptance does not establish current-run success.

The CLI is unmodified cargo-proofs 0.4.1 from upstream main at commit
`224bc1094792267e72dca5742bbcb714ec755ee6`, which includes proofs-rs PR #93.
Both profile locks record its exact source tree with no local CLI patches.
Aeneas, Charon and Lean retain their existing revisions. The upstream
`concrete_api` mode checks existing concrete word/lane API mappings, including
inherited `Clone::clone_from`. It rejects unsupported type syntax,
invalid/private/non-callable instances, non-host cfg and dependency drift.
The declaration expansion subprocess alone uses `RUSTC_BOOTSTRAP=1`; function
items are checked with the normal stable compiler. This is API discovery,
not a proof result. Standard Lean builds and theorem/axiom audits are unchanged.
No repository-specific CLI preparation hook is used.

The maintained Lake files use ordinary dependencies and select the generated
macOS arm64 models explicitly. Stage2 depends on the default proof package via
a relative path. The shared local verifier materializes separate build copies;
`scripts/record.sh [default|stage2]` records from the maintained Lake directory
using the same CLI selected by setup. Run setup first and commit/push all inputs
before recording. Recording checks maintained Lean proofs; it does not rerun
Rust-to-Lean extraction. The local verifier above performs that comparison.

The stage2 report includes a finding about reassigning `Crc.algorithm` without
rebuilding its lookup table. Its native reproduction is distinct from the
conditional formal contracts. No finding has been submitted upstream or published.
