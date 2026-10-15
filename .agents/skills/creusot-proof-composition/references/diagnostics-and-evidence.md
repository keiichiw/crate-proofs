# Diagnostics and evidence for composed proofs

## Narrow the cause in order

1. **Separate execution failures first.** Check tools/versions, translation logs, exit status, generated
   Coma, and the presence of positive roots. ICEs, Why3 server/socket failures, timeouts, and unproved
   goals are distinct states. Failure to run a solver is not a counterexample to the theorem.
   See the [common skill](../../creusot-verification/SKILL.md) for known Creusot 0.13 syntax diagnostics.
2. **Check contract sufficiency.** Inspect actual callee types, pre/postconditions, laws/refinements,
   and the relation needed by the caller in Coma and prover input. Watch reference-type trait dispatch
   and opaque-model boundaries. A closed call cannot supply contents absent from its contract.
3. **Isolate a small relation.** Use the [patterns](composition-patterns.md) to examine type/view
   conversions, empty cases, indexes, concat, witnesses, and state transitions. Prove the required
   bridges independently. Preserve the original domain and conclusion; do not eliminate goals with
   contradictory premises or added axioms.
4. **Investigate execution cost after establishing semantic relations.** Save the timeout session's
   actual SMT input and inspect repeated expansions and quantification. Split work using helpers that
   preserve definitions while controlling opacity/inlining, checked lemmas, and explicit witnesses.
   Match parallelism to CPU quota and recheck the same claim after each change.

This order narrows hypotheses rather than prescribing a cause. Record the initial symptom, attempted
change, affected VCs, and results; revisit the hypothesis if it does not help. Do not guess runtime
branches from timeout goal names or tree indexes. If the bridge closes but the caller does not,
check whether its necessary conditions reach the actual call.

### Observed boundary gaps

The incomplete percent-encoding run `percent-encoding-s43DOmha` left roots open for the encoder's
`produces_append`, `produces_refl`, and state `eq`. See the
[result history](../../../../percent-encoding/2.3.2/verification/results.md) for the status of that attempt
and the final run. Corresponding checked bridges address snoc/concat, map(empty), and integer-model/byte-view
relations. The integrated run including the new helper is recorded in the
[saved manifest](../../../../percent-encoding/2.3.2/verification/evidence/percent-encoding-J4mz7h2U/manifest.json)
and [results](../../../../percent-encoding/2.3.2/verification/results.md). This comparison demonstrates a
successful remedy for those inputs and tools, not a rule that similar timeouts always have the same cause.

### Switching solvers

The example [solver policy](../../../../percent-encoding/2.3.2/verification/assumptions.md) records Z3's
timeout/unknown result and checks the same unmodified exported SMT file with CVC5. Preserve the primary
result when a secondary solver succeeds. Save the input hash, export transformations, command, version,
budget, stdout/stderr, and exit status. Success after removing premises or assertions cannot replace
proof of the original goal.

When using a standalone solver because Why3's server is unavailable, retain the mapping from root
inventory to every exported leaf. One UNSAT SMT result does not establish the entire target. The
[lossy probe diagnostics](../../../../percent-encoding/2.3.2/verification/probes/lossy-postcondition/README.md)
show this route, but its commands and budgets are not automatically a suitable runner for another crate.
Solver results do not validate external-model adequacy or source coverage.

## Conditions for reusing dependency proofs

First pin the dependency's source, manifest, features/target, external assumptions, and exports.
The [dependency ledger](../../../../percent-encoding/2.3.2/verification/dependency-ledger.md) pins the
local `form-model` fork and its saved evidence while keeping that fork's own percent-encoding dependency
on the registry version. Inspect actual Cargo metadata edges to avoid confusing different packages
with the same name or creating cycles through a global patch. A package alias alone does not establish identity.

Next read the contract and domain used by the caller. The form encoder represents space as `+`, while
the generic percent encoder uses `%20`; they are not interchangeable algorithms. Access to an opaque
decoder's step does not supply unexported empty/suffix laws or whole-decoder equivalence. Treat local
traces and bridges as new proof work.

Finally audit dependency evidence and check actual callees in generated Coma for use of the checked
contracts. The [runner](../../../../percent-encoding/2.3.2/scripts/prove-direct.py) illustrates these checks.
An unused import, matching version label, or prose citation does not establish proof reuse. Carry the
dependency's standard-library assumptions, domains, and unverified portions into the caller's report.

## Final gates and history

Follow the target runner's format to compare source/contracts/assumptions/config/scripts/tools and
dependency evidence before and after execution, and check every target/root/leaf from fresh generated
output. Ensure new helpers and laws/refinements appear in the inventory. If reporting native results,
check that their run ID and before/after source/config hashes match the proof snapshot. The
[native fingerprint checker](../../../../percent-encoding/2.3.2/scripts/check-native-fingerprint.py)
is a concrete example; these checks do not change the finite nature of native comparisons.

An audit checks saved-bundle consistency and is separate from fresh compilation/proof. The auditor in
[common tools](../../../../verification/tools.md) and crate-local direct-SMT bundle checkers may accept
different manifest formats, so use the target version's procedure. Preserve selected/open/excluded
classifications, assumptions, source identity, and the native/formal distinction in the final report.
Take totals from the run's manifest instead of duplicating them in reusable skills.

Changing the hash of an input document also makes the old bundle cease to be evidence for current
inputs. Do not rewrite manifest hashes to make a documentation-only change pass. Preserve the old run
as history for its original inputs and rerun against new inputs when needed.

**Proposal for future runner design, not implemented:** distinguish semantic source/spec/tool inputs
from generated artifacts during input collection. The existing percent-encoding runner also includes
diagnostics and `.why3find` caches from broad probe trees, so generated-artifact changes can needlessly
invalidate a freshness audit. This does not refute the successful fresh run. Any improvement must
preserve detection of required source additions/deletions, document the input-inventory rules, and
validate them in a new run. Do not remove inputs retroactively from old manifests to force consistency.
