# Managed verification — ipnet/2.12.2

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
