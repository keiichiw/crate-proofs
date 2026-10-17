# Diagnose extraction and model boundaries

Use this reference when Charon/Aeneas fails, generated Lean does not typecheck,
or selecting more dependency bodies still does not supply the semantics needed
by a public contract. It does not prescribe new assumptions or tool upgrades.

## Locate the first failing stage

Keep the pinned versions, feature selection, command, source/configuration hashes,
exit status and diagnostic with its source location. The optional
[trial recorder](../../../../verification/trial-recording.md) preserves execution
failure separately from any accepted proof result.

| First observed failure | Inspect before changing the proof |
| --- | --- |
| Rust/Cargo | Compilation, selected features, target and toolchain compatibility |
| Charon | Rust construct, signature, trait instantiation, selected bodies and LLBC availability |
| Aeneas | LLBC operation and translation pass, context matching, borrow-state transitions, dependency selection |
| Generated Lean | Exact generated declaration and expected/actual types, including returned mutable state |
| Authored Lean or theorem audit | Contract, required relation, imported model, theorem kind and axiom dependency |

Preserve all stages reached. A failed build is not automatically a source bug;
successful extraction is not a proved API. A message containing `Exception`,
`Unreachable`, or `error` in a module/file name is not a diagnostic by itself.
The log summarizer detects selected diagnostic formats; absence of a match is
not evidence of success. Read the original diagnostic when classification is unclear.

## Follow the dependency boundary

Record a short chain:

`selected public operation → actual callee → first missing meaning → required observable`

For example, selecting an iterator collection implementation may expose an
extension helper, then reservation, length updates and pointer writes. An
available helper body does not provide the semantics of its remaining calls.
For each experiment, record the exact selected symbol, what changed, the new
generated call/type, and the remaining obligation. Change one selection or model
hypothesis at a time when that makes the result attributable.

Before selecting another body, decide what evidence would make that experiment
useful: reaching a specific translation stage, resolving a missing signature,
or supplying a checked relation needed by the caller. If successive experiments
reach the same unsupported boundary without new evidence, stop that branch,
save a blocker and work on independent scope. There is no universal retry count.

Do not make application logic opaque merely to obtain generated output. An
external model needs an explicit domain and the relevant observations; a
Formatter model without output state cannot establish rendered text, and a
capacity lemma alone cannot prove a serializer implementation. Keep conditional
helper proofs separate from actual-body API coverage.

## Minimize without changing the failing mechanism

Start from the observed construct and pinned command. Remove unrelated code while
preserving the borrow/trait/signature relationship and the same failing stage.
For mutable callbacks, retain both the return value and updated borrowed state;
for a dyn coercion, retain the concrete-to-dynamic conversion; for collection
internals, confirm the minimized case reaches the same implementation boundary.
If minimization exposes a different failure, label it a separate observation.

Save original and minimized commands, source hashes, generated fragments and
diagnostics. Record which conditions reproduce the symptom and which do not.
Distinguish an explicit unsupported operation from an internal crash or ill-typed
generated program; neither alone proves the latest upstream revision has the same
problem. Existing issue similarity is not confirmed duplication. Check current
upstream only when investigating/reporting upstream status, and keep that probe
separate from the pinned verification result.

## Re-enter the maintained proof

A successful probe is not an accepted result. Review any source/model/tool changes,
then run the target's normal extraction, correspondence checks, build and audit.
Compare theorem statements, assumptions, API mappings and exclusions as well as
names: an unchanged theorem name can conceal a stronger precondition or weaker
conclusion. Never rewrite old result hashes to make changed inputs appear verified.
