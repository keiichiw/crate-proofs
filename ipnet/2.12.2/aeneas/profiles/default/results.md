# Managed verification — ipnet/2.12.2

The current `cp` acceptance is recorded in [the cp acceptance section](#cp-acceptance--2026-10-27-macos-arm64). Earlier sections and `evidence/summary.json` retain their original input scope.

> Evidence storage: the [committed summary](evidence/summary.json) describes the original accepted inputs. Full logs and repeated snapshots are in the [local archive](evidence/archive.json), not distributed in Git. Packaging has not rerun the full proof pipeline; the checksummed compatibility fixtures remain available for fresh verification.

The [accepted macOS arm64 run — archived](evidence/archive.json) (`payload/aarch64-apple-darwin-accepted/result.json`)
passed with the archived locked configuration. Its [input archive — archived](evidence/archive.json) (`payload/aarch64-apple-darwin-accepted/archive-provenance.json`)
preserves the exact maintained inputs; historical evidence remains associated with its original inputs.

- Source archive and full file inventory checks passed before and after verification.
- Configured native tests and crate-specific regression checks completed separately from formal proof.
- Fresh extraction matched the maintained `Generated/aarch64-apple-darwin` models byte for byte.
- Standard Lake build and the transitive axiom audit passed for **625 declared theorem roots across 70 modules**. The only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- API mapping checks, tool/patch/dependency checks and runtime executable identity checks passed. Complete before/after fingerprints were equal.

The 160 mapped APIs retain the original network arithmetic and iterator contracts. Standard-library model correspondence, overflow/UB checks and checked shift contracts are required checks. This does not establish parsing/formatting or physical runtime properties outside the declared mapping.

The [specification](specification.md), theorem inventory and report mappings delimit the claims.
Extraction, the compiler and the declared standard-library/external models remain trust boundaries.
Native observations are not formal theorems and selected API proofs do not imply whole-crate verification.

This acceptance is for `aarch64-apple-darwin` only. Linux target models are kept separately;
the migrated configuration has not been executed on Linux. Historical Linux results do not certify this layout.

The current cargo-proofs patch is `c6f12abf3e1e3b6f2ec910179612f3a71d51351826f7b3c7bdb97e9df700e5eb`
(base `2446bcad7d492be2d2036629e5dc94d186a23213`, patched tree `e0a369bf354e14861a21819f366f2db0531d8d48`).
The final CLI suite passed 64 unit tests and three integration tests. All three real Lean/Aeneas integration tests were then explicitly enabled on the same final code and passed, including rejection cases.
Local managed verification requires no push. [All CLI report prerequisite checks — archived](evidence/archive.json) (`payload/cli-record-gates/result.json`) completed preparation/configuration/tool checks and reached the existing committed-and-pushed-source requirement. No new published SARIF, push or publication is claimed.
Repository scripts, preparation/native logs and patch bodies remain local evidence; SARIF proof results come from standard Lake build and the CLI’s standard Lean audit.

## 2026-10-27 macOS arm64 revalidation

The initial full verifier passed on `aarch64-apple-darwin`: fresh extraction matched the maintained generated model, the Lean build and transitive axiom audit passed for 625 theorem roots across 70 modules, and mapping checks covered 160 APIs. Runtime-check configuration and checked shift-model postchecks passed. Before and after input fingerprints matched. The default, no-default and all-features native tests also passed, separately from formal proof.

Initial local receipt: `.work/runs/default-xsxmt1br/result.json`. It applies to that run's input fingerprints; it is not a cargo-proofs SARIF recording.

Separate fresh native finding checks reproduced all eight schema rows across both Schemars versions. The heapless IPv4 fixture recorded three allocations/reallocations versus zero for the legacy control; the separate IPv6 control recorded four versus zero. Results and logs are under `.work/revalidation/2026-10-27/findings/`; these observations are not formal proof.

The final verifier run against the finished report inputs also passed. Its local receipt is `.work/runs/default-0f3d7jq3/result.json`; its before and after input fingerprints matched (`925f41b506c67e53aa46bacb488c96c4945f6bd4d3a122fb6dc0a9df7b28466b`). Its extraction, Lean audit, mapping checks and runtime/shift postchecks passed.

## cp acceptance — 2026-10-27 macOS arm64

A fresh `cp` run passed against input commit `029605b32ee36f5b23990c014bb25ae4b82600dc` after the
shared-infrastructure and ipnet-only import. This is a new execution, separate
from the historical summaries above. No contracts, maintained generated models,
source/tool locks or API mappings were changed for acceptance.

Commands, run from the repository root:

```sh
bash ipnet/2.12.2/scripts/setup.sh --offline
bash ipnet/2.12.2/scripts/verify.sh --offline
```

- Target: `aarch64-apple-darwin`; native Rust 1.91.1, extraction Rust nightly-2026-09-17 and Lean 4.35.0, with the locked Aeneas/Charon/CLI tools rechecked before reuse.
- Source inventory and reviewed standard-library inputs passed; fresh extraction matched the maintained target model.
- Default, no-default and all-features native suites passed, separately from formal proof.
- Standard Lake build passed; all **625 theorem roots in 70 modules** passed the transitive dependency/axiom audit. Only `propext`, `Classical.choice` and `Quot.sound` were allowed. All **160 API mappings** matched the theorem inventory.
- Exact runtime-check configuration and checked shift-overflow postchecks passed.
- Before/after input files were byte-identical, SHA-256 `89b1cbbb687dd638519c19bfff040cd7eff9d97b16cf52c0d6b55df584d686c4`.

All three current `proofs.toml` finding snippets were also compiled and executed
with Rust 1.91.1, offline and with locked dependencies. Each schema snippet had
its own Cargo build directory: the generated schemas rejected the serialized IPv4
values in the first finding and accepted `a/64` despite failed deserialization in
the second. The heapless replay observed three allocation/reallocation calls versus
zero for `serde` plus `ser_as_str`. Those four native executions are counterexample
observations, not formal coverage of the optional integrations.

The common Python suite completed 105 tests: 104 passed and one existing
Why3-environment check was skipped. Layout/evidence lint, active documentation links, CI configuration (ipnet only),
and exact preservation of maintained proof sources passed. Other crate trees are
unchanged from `main`. No Linux execution, cargo-proofs recording, push or publication
is claimed. The primary checked the receipts, hashes, mappings and scope; no new
independent specification or proof review is claimed for this unchanged proof package.

### Current local evidence

The complete fresh pipeline, native replay sources/locks/logs and compact acceptance
metadata were packed and independently checksum-verified. Availability is **local-only**;
a checksum is not a public download URL. Historical `evidence/archive.json` and
`evidence/summary.json` remain unchanged.

- Pipeline receipt: `.work/runs/default-t0ql8i85/result.json`, SHA-256 `2bda6bd4ccfb3ec98b4ed8dde3ce2d49a3d66f975307e76de270585bff01b2b5`.
- Native replay receipt: `.work/cp-findings/isolated-rust-q90yai1f/result.json`, SHA-256 `f77f81eae34b44836e0d26b111174b8ea65803751a263d9f8efed8acc5cc7e50`.
- Archive store: `.work/evidence-archives/`; archive SHA-256 `e60379c435bd2c9b9dee5ea61261fa144d32f1bee7cb20c5bec15243b6f97da2`.
- Archive manifest SHA-256: `7f552f6069ac806847beac8c28c5cffdb941f25474337bf1c704d863fba3b550`; 176 inventoried files.
- Exact archive members: `payload/verification/result.json`, `payload/verification/audit/result.json`, `payload/verification/inputs-before.json`, `payload/verification/inputs-after.json`, `payload/findings/result.json` and `payload/acceptance.json`.
- Local archive descriptor and full checked summary: `.work/cp-acceptance/2026-10-27-5rs98ebi/archive.json` and `summary.json` in that directory.

Recheck the retained archive without rerunning verification:

```sh
python3 scripts/aeneas_evidence.py verify \
  ipnet/2.12.2/.work/cp-acceptance/2026-10-27-5rs98ebi/archive.json \
  --store ipnet/2.12.2/.work/evidence-archives
```

This results file is an output excluded by the runner's fingerprint. Recording this
acceptance does not change the accepted proof inputs or rewrite older evidence.
