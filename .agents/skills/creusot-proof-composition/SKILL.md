---
name: creusot-proof-composition
description: Compose Creusot proofs across iterator, Cow, UTF-8, and external-model boundaries by identifying missing relations and proving checked lemmas against actual VCs. Use when bodies pass but laws, refinements, or consumers remain open, or when reviewing exactly which observations a proof guarantees.
---

# Compose Creusot proofs across boundaries

Proving a small function does not automatically carry its result into callers or trait laws that use
another model. Use this skill to identify the missing relation and connect it without changing the
meaning of the contract. First read the [common verification skill](../creusot-verification/SKILL.md)
for environment, scope, and execution, then the crate/version's `AGENTS.md` and local skill for commands and targets.

Apply this skill when model types or abstraction levels differ, an iterator consumer or law remains
open, an external API guarantee does not reach its wrapper, or a closed VC's meaning needs review.
For provenance capture alone, use the [common tools](../../../verification/tools.md); for a new crate's
scope, use the [playbook](../../../verification/playbook.md).
Solver tuning cannot supply unspecified standard-library behavior.

## 1. Fix the claim under investigation

Read the specification, assumptions ledger, API/generated-target inventory, and the corresponding
actual Coma and root goal. State in one sentence whether the claim concerns a body, trait refinement,
law, consumer, or standard-library boundary. Then write the relation the caller needs alongside the
relation the callee actually provides, including their types. Distinguish, for example, equality of
`Seq<Int>` from equality of `Seq<u8>`, or scalar concatenation from UTF-8 byte concatenation.
Do not infer the failing runtime branch from a goal name alone.

For external models, check the assumptions authorized for this task and their conditions in the ledger.
Approval or success in another crate is not blanket permission for new assumptions.
If a required fact is absent from the contract, keep that boundary unresolved. Distinguish a bridge
derivable from existing contracts from a change requiring a new external assumption.
Do not fill the gap by marking application algorithms `trusted` or weakening contracts.

Record the claim, missing relation, actual goal/input location, and applicable assumptions.
Read only the reference needed for the observed symptom.

| Observed symptom | Check next | Reference |
| --- | --- | --- |
| Only equality remains open | View/deep-model types, lengths, and pointwise relations | [Equality bridge](references/composition-patterns.md#carry-equality-across-views) |
| Loop step, empty input, or refl/trans remains open | Which empty, map, concat, suffix, or snoc law is missing | [Sequence boundaries](references/composition-patterns.md#prove-sequence-boundaries-in-small-steps) |
| `next` passes but collection does not | Connections among remaining state, produced sequence, and accumulated output | [Iterator composition](references/composition-patterns.md#connect-an-iterator-to-its-consumer) |
| Cow/UTF-8 contents or variants do not connect | Scalar/byte views, concrete-type contracts, and existing postcondition witnesses | [Cow and UTF-8](references/composition-patterns.md#separate-cow-and-utf-8-guarantees) |
| Formatter VCs close without an output guarantee | Whether the contract covers calls, results, request traces, or rendered contents | [Observation scope](references/composition-patterns.md#separate-callback-arguments-from-external-effects) |
| Timeout, translation error, or ineffective dependency model | Actual callee/SMT, exported laws, tools, and execution conditions | [Diagnostic order](references/diagnostics-and-evidence.md#narrow-the-cause-in-order) |

## 2. Prove the smallest checked bridge first

Express the missing relation as a pure lemma or a small wrapper contract. Make lengths, index ranges,
empty/nonempty cases, and recursive decreases explicit. Prove the helper itself as a separate target
with positive goals before using it in the caller. Asserting the conclusion in a caller is not a
substitute for proving the relation. Even a lemma returning `true` needs its postcondition VC closed.

Reuse a dependency only through its public checked contracts and their domains. Do not infer an
opaque model's unexported base case or equivalence with another algorithm. Prove missing relations
locally and check actual use and dependency evidence under the
[reuse conditions](references/diagnostics-and-evidence.md#conditions-for-reusing-dependency-proofs).

When a small probe passes, record its types, preconditions, external models, and tool version.
Do not update production API status from a successful probe alone.

## 3. Compose without changing the meaning

Connect the bridge at the relevant caller branch. For a consumer, maintain loop invariants relating
initial state, visited sequence, current state, and accumulated value. Check initialization, one step,
and termination. Track state equality, output contents, ownership variant, and error propagation as separate contracts.

If proof remains open, return to the [diagnostic order](references/diagnostics-and-evidence.md#narrow-the-cause-in-order).
Check missing semantic relations before expression expansion and solver budgets. Preserve definitions,
assumptions, and guarantees when splitting lemmas or exposing witnesses. If runtime code changes,
record its diff and native correspondence checks. Decide whether to continue, narrow scope, or stop
from observed blockers and cost; do not silently exclude unresolved targets.

## 4. Establish the composed scope with evidence

Completion requires the crate's fresh runner to classify every generated target, including helpers,
callers, generated implementations, and laws/refinements, and close the selected positive roots and
all their leaves. Check expected-open/excluded targets and reasons, before/after input and tool
fingerprints, dependency evidence, and exit status. Earlier probes, isolated solver successes, and
audits of old bundles do not replace this integrated run.

Report which contents, states, or observations were proved, under which domains and external assumptions.
Present native comparisons as separate evidence matched to the same source. Do not extend request
traces to rendered output, Cow variants to allocation/pointer identity, `next` to unselected standard
iterator defaults, or a fork proof to all-input upstream equivalence. Keep counts and current status
in the run's manifest instead of duplicating fixed totals here. See
[final gates and history](references/diagnostics-and-evidence.md#final-gates-and-history) for evidence reuse and preservation.
