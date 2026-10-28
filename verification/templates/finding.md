# <ID>: <observable failure>

## Identity and classification

- ID: `<CRATE>-<NNN>` (stable within this crate/version)
- Crate/version: `<name>/<version>`
- Component: `<release implementation | dependency | Charon | Aeneas | Lean backend | repo tooling>`
- Kind: `<implementation-bug | documentation-mismatch | tool-defect | unsupported-boundary | specification-question | environment-failure>`
- Confidence: `<suspected | source-reviewed | reproduced-at-pinned-inputs>`
- Resolution: `<open | workaround | fixed-at-pinned-revision | not-a-bug>`
- First observed / last reproduced: `<date or unknown>`
- Upstream report: `<not-reported | exact issue URL>`
- Upstream fix: `<not-checked | exact revision and tested result>`

## Pinned inputs

Record the source.lock.json path and digest, release archive checksum or full Git
revision, affected source/API locations, profile, host and Rust target, features,
Rust/verification tool revisions, and debug/release overflow settings. A current
lock is not proof of the inputs used by a historical observation.

## Expected behavior and its basis

State the independent expected result, error, consumed input and post-state.
Cite the release documentation, mathematical specification or language rule.
List preconditions and show why the counterexample satisfies them. Distinguish a
documented API violation from failure of a stronger desired contract.

## Observed behavior

Give the smallest concrete input and exact return value/panic/diagnostic, residual
input and state. Identify the first failing stage. Record controls that succeed.
Do not infer other types, features, targets or async behavior from one execution.

## Reproduction

- Reproducer: `<version-relative source/test path and digest>`
- Working directory: `<repo root or exact version-relative directory>`
- Prerequisites: `<setup/profile and pinned environment>`
- Command: `<exact argv or command; fresh .work output>`
- Exit status and observation: `<recorded value>`
- Last independently rerun: `<date or not rerun>`

The command must use unchanged pinned source. State whether it is currently
runnable or a historical command requiring restored inputs. Keep the minimized
reproducer checked in; put execution logs/build output under ignored .work.

## Evidence and interpretation

Reference original records with their SHA-256. For archived evidence include the
archive descriptor, archive digest and exact member, plus availability (local-only
or an actual public retrieval URL). Do not invent a URL from a hash. State which
claims are native observations, source analysis or checked formal theorems.

## Cause, impact and proof scope

Explain the source/model boundary and affected public behavior. Separate confirmed
cause from hypotheses. Record affected proofs, excluded APIs and any additional
premises introduced by a workaround. An extractor failure is not automatically a
crate bug, and proving erroneous behavior is not the desired correctness theorem.

## Resolution and regression

Record a proposed fix separately from the pinned source, regression case/location,
workaround limits and results against any checked fix revision. Reporting or pushing
upstream requires separate authorization. Append dated updates; preserve original
counterexamples and evidence identities when status changes.
