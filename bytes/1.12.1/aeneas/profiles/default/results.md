# Managed verification — bytes/1.12.1

> Evidence storage: the [committed summary](evidence/summary.json) describes the original accepted inputs. Full logs and repeated snapshots are in the [local archive](evidence/archive.json), not distributed in Git. Packaging has not rerun the full proof pipeline; the checksummed compatibility fixtures remain available for fresh verification.

The [accepted macOS arm64 run — archived](evidence/archive.json) (`payload/aarch64-apple-darwin-accepted/result.json`)
passed with the archived locked configuration. Its [input archive — archived](evidence/archive.json) (`payload/aarch64-apple-darwin-accepted/archive-provenance.json`)
preserves the exact maintained inputs; historical evidence remains associated with its original inputs.

- Source archive and full file inventory checks passed before and after verification.
- Configured native tests and crate-specific regression checks completed separately from formal proof.
- Fresh extraction matched the maintained `Generated/aarch64-apple-darwin` models byte for byte.
- Standard Lake build and the transitive axiom audit passed for **161 declared theorem roots across 22 modules**. The only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- API mapping checks, tool/patch/dependency checks and runtime executable identity checks passed. Complete before/after fingerprints were equal.

The 56 mapped APIs preserve the independent specification, including its signed-reader discrepancy and explicit unsafe/whole-crate exclusions. All 161 theorem roots include the accepted stage3 extension. Native default and no-default suites are separate from formal proof. Core, numeric and stage3 patched extractors plus an ordinary negative control remain separately locked. Mandatory shared-reborrow, declaration-order, branch-join, rooted extraction, never-type and signed-read regression checks passed. Four adversarial input-guard tests separately reject an empty prelude correspondence, changed manifest semantics, missing repair delta and a captured standard-source symlink.

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

## Findings reorganization

This main-based branch imports the bytes profile from develop commit
`0af93f1c558101bbae5e84dac8bbf95f77794672`. Report prose and Finding API associations
were updated; all tool/proof mappings, generated Lean, specifications, patches,
locks and historical evidence retain their develop contents. These editorial
changes alter verification inputs. No fresh full extraction/build/axiom audit or
publishable SARIF is claimed. See the [reorganization record](../../../verification/reorganization.md)
for separate source checks, archive integrity checks and the new native replay.
