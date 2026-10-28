# Crate verification playbook

First establish upstream identity and assess the feasibility of a small pure core. Use contracts, evidence, and cost to determine the verification scope. Do not confuse the crate name or number of public APIs with the verified scope.

In the httpdate 1.0.3 example, work expanded in stages from the byte parser and calendar core to the raw grammar, a bridge to the public type with calendar validity, wrappers, and selected trait methods.
The result covers only the selected functions and contracts in that fork. See the
[specification](../httpdate/1.0.3/verification/specification.md),
[coverage](../httpdate/1.0.3/verification/coverage.md),
[correspondence audit](../httpdate/1.0.3/verification/correspondence/README.md) for details.
This does not promise the same feasibility or results for later crates.

## 1. Fix the candidate and its provenance

1. Record the target crate, purpose, and users. Before choosing a version, independent investigation such as an inventory of candidate APIs and dependencies may proceed. Choose the exact version before release capture and proof; do not identify the target only by a crate name such as hyper or atoi.
2. Record the public registry version API and checksum, distributed archive, and, where available, upstream tag / commit as separate identities. Compare the archive checksum with VCS metadata. The same version label does not guarantee that a release archive and Git tree are the same.
3. Keep local inputs separate from output locations. Use [`scripts/capture-crate-release.py`](../scripts/capture-crate-release.py) for reusable release captures.
   `NAME VERSION --output DIR` fetches registry metadata and the archive over HTTPS.
   Check an existing capture offline with `--check DIR`. An offline capture passes both the metadata response and archive, for example `NAME VERSION --output DIR --metadata-file RESPONSE --archive-file ARCHIVE`. The tool checks the checksum and the file inventory after extracting the archive, but does not check identity with the Git tree, identity with a fork, build, or proof. A later `--check` does not re-query the current authenticity of the source.
4. Inventory the package manifest, workspace, features, targets, build scripts, dependency crates, MSRV, `no_std`, unsafe code, macros / proc macros, and runtime / async behavior. Do not describe verification of default features alone as a guarantee for the whole crate.
5. When setting proof scope, record the exact crate/version, archive checksum, available source commit, and selected features and target in the plan. If dependencies or platform are undecided, continue investigating and keep them marked as blockers / unreviewed.

## 2. Assess the core before spending heavily

Start with a small pure function or a finite transition with explicit state. Ask whether meaningful preconditions and postconditions can be written for each function, not just whether the Rust syntax can be translated.

- **Parser / decoder:** Check input slice bounds, successful values, failure conditions, consumed byte count or remaining slice, overflow, and short inputs. For an atoi candidate, record sign, empty input, whitespace, radix, stopping digits, overflow, and return value / error / consumed length per API, based on upstream source and contracts. These are investigation questions, not specifications asserted here.
- **Protocol parser:** If a permissive wire grammar differs from a domain-valid public type, make the boundary between a raw parse record and invariant-bearing value explicit. Do not assume that a successful raw parse automatically means the date, length, or state is valid.
- **State machine:** First investigate whether pure transition functions and state invariants can be extracted. Message-framing transitions may be candidates in hyper. Depending on the target version, types such as `HeaderValue`, `Method`, and `StatusCode` may be owned by the `http` dependency and re-exported by hyper. Check source and ownership for the exact version; do not count a proof of those types themselves as verification of hyper's implementation. This is a scope candidate, not a guarantee about hyper's functionality. Assess async scheduling, runtime, network IO, unsafe code, and large generic trait boundaries individually as outside the initial core. Do not declare something possible or impossible based only on the number of dependencies.
- **Type conversion:** List every constructor path from raw/private types to public types and check whether each path that establishes an invariant can have a checked contract.
- **External calls:** If std / dependencies / callbacks lack specifications, do not infer their preconditions, return values, errors, panics, or side effects. A small probe checks only whether translation is feasible; it does not prove the semantics of a production API.

First inventory candidate standard-library and dependency models, and see whether the trust boundary can be narrowed. Record models in a separate ledger with source / tool version, domain, platform, and properties not guaranteed. Do not add `trusted` declarations or assumptions to application algorithms to make a proof pass. If a conditional model is needed, consider a checked contract connecting the condition to the call site.

## 3. Design contracts and correspondence

1. Specify each API's successful value / relation, failure conditions, input consumption, overflow, and boundary values. Parsers must cover error branches and consumed prefixes as well as success. State explicitly which behaviors are outside the contract.
2. Prepare small reusable helpers and laws first. Prove byte grammar uniqueness, slice/string relations, state-transition preservation, and similar properties as independent checked lemmas; do not bridge the implementation and contract using only caller assertions.
3. Limit callback / IO API contracts according to result conditions. For example, describe output only when the result is `Ok` and the sink faithfully appends. Guarantees for arbitrary or transforming sinks, partial output on `Err`, or callback panics require a separately implementable model and evidence.
4. Connect each proof claim to the upstream runtime text. Distinguish annotation-only changes from runtime changes, and explain extraction, branch order, error paths, type / trait dispatch, and callback order. For lines where runtime changes, provide the reason and native correspondence evidence.
5. Report native tests / finite differential observations separately as observations of tested inputs, options, and error chunks. Do not count them as upstream equivalence over all inputs, formal proof, or a substitute for trust assumptions.

The httpdate parser separated permissive `RawDate` from `HttpDate`, which carries a calendar invariant, and added a checked bridge between raw grammar and public validation. It explicitly preserved upstream acceptance behavior, such as an unchecked separator in RFC850, instead of adopting an idealized grammar. It specified error conditions as well as ordinary successful behavior. The formatter contract was limited to `Ok` plus append conditions, and native failing-writer comparisons recorded the write chunks for a finite set of error thresholds.

## 4. Preserve run evidence and freshness

For Aeneas, use the [new-crate procedure](templates/aeneas-managed/README.md) and
managed setup/verify wrappers. Do not activate the Creusot environment. The Why3,
Coma and shared activation instructions below apply to Creusot targets only.

Read the existing proof procedure, crate-local `AGENTS.md`, and skill first. Activate the shared repository environment, and use a separate workspace / lockfile / evidence directory for each crate.

- Before compile, record source, contracts/specification, configuration, scripts, toolchain / prover versions and hashes in the manifest. Run in a fresh output location with the proof cache disabled.
- Keep native tests, proof runs, and upstream differential runs in separate logs and results.
- Recheck input fingerprints after proof. Reconstruct the root goal inventory using Why3 or similar and compare it with each target's `proof.json`. Distinguish selected, expected-open, and excluded targets.
- Confirm there are positive root goals, none are missing, each selected goal tree succeeds, and the process exits normally. Do not count zero goals, missing goals, stale cache, timeouts, or abnormal exits as success.
- To audit a verified directory, use [`scripts/audit-proof-evidence.py`](../scripts/audit-proof-evidence.py).
  Check `VERSION_DIRECTORY` read-only. If needed, use `--reconstruct-root-goals` to reconstruct the root inventory saved in Coma from Why3, and compare it with the manifest's selected / open / excluded inventory and the complete Coma output tree passed with `--generated-dir PATH`. If the bundle does not contain Coma for excluded targets, the latter requires the original complete Coma output tree. Use `--source-root PATH` to specify a Rust source tree other than the default `VERSION_DIRECTORY/crate/src`. The audit compares recorded fingerprints with listed inputs, Rust source inventory, and saved sessions, but does not rerun the SMT prover or recheck proof certificates. It also cannot find missing non-Rust inputs that were not recorded in the manifest. Therefore it is not a replacement for a fresh crate runner, proof of all feature/API scope, or independent proof that the run was actually fresh. The mere existence of a past manifest does not establish a fresh proof.
- Confirm with small corruption guards that the checker rejects changed source, zero / missing goals, target inventory differences, open classification issues, and abnormal exits. Guards do not count as formal goals.
- Take coverage document counts from the manifest at the time of update. Do not copy fixed counts into the workflow or this playbook. Identify unselected APIs, unsupported features, platforms, and open goals.

The httpdate manifest recorded `cache: false`, input fingerprints, target Coma / proof hashes, root goal names, and status, and compared the goal inventory through Why3 reconstruction. This audit did not rerun or recheck SMT proof certificates. Coverage counts describe that specific run and do not carry forward after source changes. Its correspondence manifest combined the formal manifest hash with reference/runtime source hashes, but native comparison remains a finite observation. These evidence formats can be reused; their particular counts and results cannot be transferred to another crate.

## 5. Decide whether to continue or stop

Set a short feasibility milestone.

1. **Inventory:** Establish provenance, feature/API map, dependencies, platform, and unsafe boundaries.
2. **Core proof:** Prove roughly 1–3 important pure core functions with contracts and fresh evidence. Check root goals and semantics even if compilation succeeds.
3. **Boundary review:** Review missing contracts, excessive assumptions, runtime differences, translation blockers, and VC instability to decide whether to proceed to the next small subset of planned APIs.
4. **Scope review:** Record whether to continue, narrow scope, or stop. Keep failed probes and open goals; do not weaken contracts to make the successful scope look broader.

Use Luna-like procedures for ordinary investigation and implementation. Request Astra-like review if blocked on difficult SMT / Creusot behavior or specification boundaries. Follow the user's model preference if one is given. Set an execution-time / token budget up front and reconsider the value of continuing at the milestone. Do not remove proof content, input scope, or freshness conditions for speed.

## Reusable diagnostic notes

- If Creusot 0.13 ICEs on MIR byte-string / slice patterns, save the diagnostic and minimal reproduction; try scalar byte comparisons or tuple matching. For ghost numeric byte predicates, use `@` and Pearlite, and explicitly open the needed fields after `open(self)`.
- On timeout, do not infer a runtime branch from the tree index or goal name. Open the actual prover input saved by the timeout session and inspect assumptions and goal. For deriving byte inequality from sequence inequality, assess whether a separate extensional-equality bridge is needed.
- Include helper law / trait method targets, generated impls, and refinements in the inventory. A method body proof and a trait refinement are separate claims. If a method such as Clone has no meaningful postcondition and zero VCs, do not say its semantics were proved.
- Check constructors for type invariants, the relation between an array index and the whole array, the generic dispatch target, and callback contracts in generated Coma and call preconditions. Do not infer them from successful compilation.
- If inlining a large expression makes prover input grow, inspect the actual input and consider a definition-preserving model, checked bridge, or split helper. Match parallelism to the CPU quota.

These diagnostics reflect Creusot-specific experience and do not automatically apply to other verifiers. Before beginning work on a crate, reread the [shared Creusot skill](../.agents/skills/creusot-verification/SKILL.md)
and that crate's instructions.
