# Local macOS arm64 verification tools

The local bootstrap installs the pinned Creusot 0.13.0 and cargo-proofs 0.3.4 source revisions, Rust 1.91.0 and nightly-2026-06-22, the pinned Why3/Why3find sources, and the prover versions selected by Creusot. It uses the native Apple Silicon toolchain. Creusot's CVC4 download is an Intel macOS executable and requires Rosetta; the other supplied prover downloads are arm64.

Run from the repository root:

```bash
bash scripts/setup-local-macos.sh
source scripts/activate-local.sh
bash scripts/check-local-tools.sh
```

Prerequisites are Bash 4 or newer (the macOS system Bash 3 is insufficient), Xcode command-line tools, Git, curl, Rustup/Cargo, Opam, Python 3, unzip, make, pkg-config, autoconf, and automake. The bootstrap stops on a missing prerequisite. It downloads and builds the pinned sources and needs network access and free disk space.

Rust toolchains, Cargo packages/binaries, Opam root and switch, Creusot models, sources, and sample proof logs live under `.local-verification/`, which is ignored by Git. No shell startup file is edited. Activation applies to the current shell; a new shell retains the existing user toolchain. The upstream Creusot launcher still uses the macOS user Why3 preferences location and its download cache, so these two locations are shared with an existing installation. The bootstrap avoids the upstream macOS installer step that would replace the user's `~/.creusot` Opam switch.

The setup invokes a fresh sample proof as its final step. A successful check saves `versions.txt`, `prove.log`, generated Coma and proof sessions, and `result.json` under `.local-verification/smoke/run-*/`. It requires positive closed goals and records installed tool hashes. This establishes local tool operation, not successful verification of any repository crate.

The completed bootstrap check is recorded in [local-macos-validation.json](local-macos-validation.json). The exact installed Opam package set is exported in `.local-verification/opam-switch.export`. The sample passed with fresh generated obligations and no proof-cache reuse; crate refresh status is recorded in the version-specific results pages.

## Platform and evidence scope

Historical project evidence was produced on Linux. For native macOS refreshes, httpdate's `SystemTime` model has been reviewed against both pinned Rust source revisions; see its [assumptions ledger](../httpdate/1.0.3/verification/stdlib-assumptions.md) and [platform review](../httpdate/1.0.3/verification/platform-review/review.json). This is a documented model assumption, not a proof of the Rust standard library. Native and differential tests are rerun separately.

The per-crate runners now source `scripts/activate.sh`, which selects this isolated installation on macOS and retains the cloud configuration on Linux. Dependency fingerprint collectors resolve the locked local Cargo metadata, and archive promotion supports macOS. httpdate uses a fingerprinted version-local Why3 configuration with Z3, Alt-Ergo, and CVC5. CVC5 uses per-query time limits because its global timer caused worker exit to stall on macOS; CVC4 is disabled. The runner invokes Why3find directly because cargo-creusot overrides the configuration environment variable. A successful smoke check alone does not complete the [evidence refresh](refresh.md).
