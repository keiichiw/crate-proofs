# Crate verification plan

Use this plan to investigate candidates and determine scope. If identity or proof scope items are undecided, record their status and blockers and continue the investigation. Do not begin a proof for that scope until the exact target version and scope have been selected and the required provenance fixed. Fill in the manifest and execution results after the proof. Do not describe the whole crate as verified unless the selected targets match the actual evidence.

## Identity and provenance

- Crate / exact version:
- Registry archive SHA-256:
- Registry provenance source and capture date:
- Upstream repository / tag or commit:
- Relationship between archive and VCS tree:
- Capture directory and command:
- Rust / verifier / prover versions:
- Undecided identity or provenance items / blocker:

## Build surface

- Default and optional features:
- Public modules, APIs, traits, constructors:
- Target platforms / `no_std` / MSRV:
- Dependency tree and relevant versions:
- Build scripts, proc macros, generated code:
- Unsafe blocks and FFI:
- Async / runtime / network / callback boundaries:
- Candidate core subset and rationale:
- Undecided feature / ownership / dependency items / blocker:

## Contracts and scope

| API / helper | Intended precondition | Success postcondition | Error / consumed-prefix behavior | Invariant bridge | Status |
| --- | --- | --- | --- | --- | --- |
|  |  |  |  |  | unreviewed |

- Feature / target selection:
- Explicit exclusions:
- Open or expected-open goals and reason:
- Required helper laws / trait refinements:
- Unsupported error, overflow, panic, IO, or callback behavior:

## Trust and correspondence

| External boundary / assumption | Exact domain and platform | Source / version / hash | Guaranteed behavior | Not guaranteed |
| --- | --- | --- | --- | --- |
|  |  |  |  |  |

- Application-level `trusted` declarations: must be none; if any appear, stop and redesign scope.
- Runtime source changed from release? List function and behavioral reason:
- Annotation-only changes:
- Upstream correspondence method and limits:
- Native tests / differential observations and finite input description:

## Evidence and decision

- Fresh output directory:
- Pre-run fingerprints:
- Proof command / cache setting:
- Post-run fingerprint check:
- Root-goal inventory source and checker result:
- Selected targets: fill from the current manifest only.
- Closed / open / excluded targets: fill from the current manifest only.
- Native test result (separate from formal proof):
- Differential result and observation limits:
- Remaining blockers / translation diagnostics:
- Time and token budget; milestone date:
- Decision: continue / narrow / stop; rationale:
- Unreviewed items that remain blockers:

## Stop conditions

- Release identity or selected feature surface is unclear.
- A key core contract cannot express the intended behavior, or the only route relies on
  application-level `trusted` assumptions or an unmodeled external call.
- Evidence has stale or changed inputs, cache reuse, zero/missing goals, unclassified open goals,
  incomplete target inventory, or abnormal termination.
- Runtime changes cannot be connected to upstream behavior within the available correspondence
  evidence.
- Milestone cost exceeds the agreed budget without evidence that a narrower useful scope is viable.

Use the repository-root `verification/playbook.md` for the workflow and the target version's own
`AGENTS.md` and skill for commands. Copy this template under the target version's
`verification/plan.md`; it records a decision and does not itself establish proof.
