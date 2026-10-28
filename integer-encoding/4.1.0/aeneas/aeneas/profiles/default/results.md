# Managed verification — integer-encoding/4.1.0

> Evidence storage: the [committed summary](evidence/summary.json) describes the original accepted inputs. Full logs and repeated snapshots are in the [local archive](evidence/archive.json), not distributed in Git. Packaging has not rerun the full proof pipeline; current verification does not consume historical fixtures.

The [accepted macOS arm64 run — archived](evidence/archive.json) (`payload/aarch64-apple-darwin-accepted/result.json`)
passed with the archived locked configuration. Its [input archive — archived](evidence/archive.json) (`payload/aarch64-apple-darwin-accepted/archive-provenance.json`)
preserves the exact maintained inputs; historical evidence remains associated with its original inputs.

- Source archive and full file inventory checks passed before and after verification.
- Configured native tests and crate-specific regression checks completed separately from formal proof.
- Fresh extraction matched the maintained `Generated/aarch64-apple-darwin` models byte for byte.
- Standard Lake build and the transitive axiom audit passed for **163 declared theorem roots across 11 modules**. The only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- API mapping checks, tool/patch/dependency checks and runtime executable identity checks passed. Complete before/after fingerprints were equal.

The 80 mapped APIs cover the selected built-in scalar scope, not all 90 candidates. Current verification uses the current locked release source, configuration, specifications, proof packages and regression inputs. It checks the selected fixed-integer model boundaries and does not read historical evidence archives or CRC input maps. Earlier archive-based checks are historical provenance and apply to their original inputs.

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

## Current-input verification (2026-10-23)

Fresh macOS arm64 verification passed using the current source, configuration,
proof packages and regression inputs, without historical evidence inputs. This
run completed the configured native checks and oracles, fresh extraction/model
comparisons, standard Lake build, named theorem/axiom audits and unchanged
before/after fingerprints. It establishes only this profile's stated contracts.

Local-only result: [result.json](/Users/keiichiw/workspace/crate-proofs/.work/current-input-refactor/isolated-checkout/integer-encoding/4.1.0/.work/runs/default-iwb374br/result.json), SHA-256 `46cbf28698e49d31176d32cca0bee7e78e7a714c63869a95048c856b0fdd46e7`.
Input fingerprint: SHA-256 `cc5883dcc4667f5d129a4a4de8e0e98db60cf1eae4a7924d49f0cbc705e526d4`. Linux was not run for this result.

## October 27, 2026 revalidation

The managed verifier passed on `aarch64-apple-darwin` before report integration. Fresh extraction matched the maintained models, the Lean build and audit passed for 163 theorem roots across 11 modules, and API mapping checks passed for the 80 selected scalar APIs. Before-and-after input fingerprints matched. The local run receipt is `.work/runs/default-cjuc1vsk/result.json`.

Native checks were separate from formal proof: the harness passed 15 tests in each of debug and release, the upstream suite passed 31 tests, and one documentation example passed. The native reproducer also confirmed the synchronous observations for IE-S1, IE-S2 and IE-G1 in both profiles. These observations do not extend formal API coverage.

The first post-integration attempt, `.work/runs/default-4o8sv7k9`, failed at the inventory check because it compared the entire report file against the old generated text. The inventory check was adjusted to preserve human-authored report prose while checking the complete parsed tool configuration and its ordered 80 mappings, and retaining byte-exact theorem inventory checks. Positive, negative and regeneration checks passed in an isolated copy; this change does not alter the proof obligations. The failed run is retained.

**Post-integration verification:** the final managed run passed on `aarch64-apple-darwin`; its receipt is `.work/runs/default-cy4iwqyu/result.json`. The audit passed for all 163 roots and the API mappings. Before-and-after input fingerprints matched (SHA-256 `5f5ee12685808bacb7d2d573f086c64389d0b8837004f09664c08d7a900cf2f9`).

The exact pinned registry reproductions for IE-S1, IE-S2, IE-G1 and IE-D1 each passed their assertions in both debug and release, with independent build directories. IE-D2 is based on documentation and source review; no big-endian native execution is claimed.
