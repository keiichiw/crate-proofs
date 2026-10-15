---
name: creusot-verification
description: Procedures for Rust contract design, formal verification, and evidence review using Creusot.
---

# Creusot Verification

For a new crate/version, first use the [playbook](../../../verification/playbook.md) and
[plan template](../../../verification/templates/crate-plan.md) to organize the important pure core,
the crate that owns the implementation, features/platforms, success and failure contracts, and external dependencies. Keep undecided items as blockers and proceed with the parts that can be investigated independently. For atoi, assess digit consumption, sign, and overflow separately; for hyper, assess message framing and state transitions separately from async/runtime boundaries.
If headers, methods, or other items are implemented or re-exported by a dependency crate, distinguish that owning crate from the verification target.

1. Choose the execution environment before running commands. For the recorded Linux cloud environment, run `source scripts/activate.sh`; for native macOS arm64 tools, follow [the local setup guide](../../../verification/local-macos.md) and run `source scripts/activate-local.sh`. A working local bootstrap does not port cloud-specific runners or extend Linux-specific model assumptions: review those before a crate evidence claim. x86_64 is not a general verification requirement. The Codex cloud environment is isolated, so do not create an additional worktree there.
2. Read the target version's `AGENTS.md`, dedicated skill, specification, coverage, implementation, and native tests. Confirm the guaranteed properties and APIs that are out of scope. If trial/method documents exist, also read their purpose, boundaries, trusted model assumptions, and related evidence. Use a separate Cargo workspace and evidence directory for each version.
3. Contracts express intended behavior. Do not weaken contracts to get a proof to pass, or add `trusted` / assumptions to application logic. Separate and ledger any necessary standard-library model; show its scope of application and properties it does not guarantee in review.
4. A successful compile does not guarantee semantics. An extern call without a contract may create an impossible precondition. Prove all goals for each target function and generated implementation, helper lemma, and trait law in a fresh output directory. Check for a positive goal count, target VCs, all goal trees, and a successful exit state. Do not count zero, missing, or unresolved goals as a successful proof.
5. Record hashes and versions of input sources, configuration, and tools before compile, then check after proof that the inputs have not changed. Save compile/proof logs and machine-readable results, and watch for artifacts that appear to reuse existing results.
6. If ordinary Rust syntax triggers an ICE in Creusot 0.13, save and minimize the diagnostic. MIR byte-string / slice pattern ICEs have occurred; for byte cores, consider comparing a single byte or using tuple matching. For ghost numeric byte predicates, use `@` and Pearlite, and explicitly open the fields needed from the `open(self)` model. On a timeout, do not infer a runtime branch from the tree index or goal name. Open the actual prover input saved by the timeout session and inspect its assumptions and goal. A helper contract may need a separately verified extensional-equality bridge to derive individual byte inequality from a structural sequence inequality.
7. Investigate standard-library boundaries with small probes. Do not confuse probe compile/proof results or abstract trait models with proofs of product APIs, and do not infer semantics for calls without external specifications. Limit trusted models to standard-library boundaries and state their assumptions, target platform, and properties they do not guarantee. Do not trust application computations or algorithms.
8. Report native tests, upstream differential tests, and formal proofs as separate evidence. Differential tests show agreement observed on tested inputs, not formal upstream equivalence for all inputs. Update coverage documents based on actual runs/evidence and identify unrun or unproved scope. Take goal totals from the current manifest; do not duplicate unstable totals in skills or inventories.
9. Do not log in, push, publish, or deploy unless the user explicitly authorizes it.

Ask primary about unclear specifications, contracts, or evidence. Consult Astra when blocked on Creusot proof behavior or specification design; use Luna's workflow for ordinary investigation and implementation.

## Keep scope, status, and evidence consistent

- Read both scope documents and the post-run results page before describing the latest status. For form_urlencoded and percent-encoding, `verification/results.md` owns run status; httpdate currently uses `verification/coverage.md`. A provisional paragraph in an input document must not override a later completed manifest.
- Keep contracts, scope, exclusions, assumptions, and target inventories in fingerprinted inputs. Keep run IDs, counts, outcomes, freshness, and execution blockers in one post-run status page that the runner does not fingerprint. Other guides link there rather than duplicating transient status. Do not remove proof-relevant inputs from fingerprinting just to obtain a passing audit.
- Before freezing inputs, reconcile README navigation, version guides, plan, coverage, API inventory, assumptions, and skills. Remove superseded provisional status from scope documents and broken references to removed artifacts. Include every maintained crate/version in the root guide without copying goal totals there.
- After the complete proof and separate native checks, update the status page from the actual manifest and audit, including remaining open/excluded targets. Check the runner's input collection before editing that page; if it is fingerprinted, separate status from scope before the run. A post-run documentation edit must not silently invalidate the new result.
- A hash change requires a fresh run, not rewriting an old manifest. Preserve historical bundles. Audit and regenerate dependency evidence before dependents, then review their immutable evidence pins before freezing dependent inputs. Report unavailable environments or failed runs as pending; do not promote partial evidence or move a successful pointer to it.

## Shared tools and public reports

- Refer to the [shared tool procedures and formats](../../../verification/tools.md).
  `scripts/capture-crate-release.py NAME VERSION --output DIRECTORY` saves a distributed archive
  after checking it against the registry checksum, and `--check DIRECTORY` rechecks it offline.
  A Git commit, working tree claiming the same version, distributed archive, and verification fork are distinct identities.
  Consistency of saved metadata alone does not establish current registry authenticity or fork equivalence.
- `scripts/audit-proof-evidence.py VERSION_DIRECTORY --reconstruct-root-goals` audits a saved bundle
  read-only. It is not a substitute for a fresh per-version runner and does not recheck SMT or certificates.
  Also specify `--generated-dir DIRECTORY` to compare the complete generated inventory.
  Do not move crate-specific target lists, date domains, or standard-library models into shared tools.
- If runtime changes in a verification fork, record the upstream-to-fork function map and the inputs and observation limits of differential tests.
  Compare grammar quirks, short-circuit order, typed trait dispatch, and callback call sequences as well.
  Do not call agreement on the same source version or finite tests formal upstream equivalence.
- Report behavior outside the model, such as external callback panics, IO side effects, and allocation.
  Report body proofs, trait refinements, and unselected inherited/default methods separately.
- Recording results in proofs.rs is a separate step. The inspected cargo-proofs 0.3.4 Creusot importer records
  only `panic_contract`; functional correctness and `no_ub` are not claims made by that importer.
  For API records, check source spans and catalogue mapping, and do not hide an open refinement behind a successful body proof.
  `publish --dry-run` may still be a server operation. Do not run it for a request only to prepare an unpublished report.

Use a short feasibility milestone to assess time/token costs, unsupported syntax, dependency models, and contract difficulty.
Record whether to proceed to the next important subset, narrow scope, or stop. Expanding scope to the whole crate is not a success condition. Share only procedures and checks that are actually reusable; do not automatically apply external models or crate-specific types/grammars to other crates.

## Reusable notes at specification boundaries

- If an input grammar differs from a public-value invariant, separate a permissive raw record from the validated public type. Do not silently assume validity for the public type; put a checked contract on the conversion bridge and every constructor path.
- If the implementation can panic in part of the `SystemTime` domain, do not make a bounded body proof imply an unconditional trait refinement. The public `From<SystemTime>` trait method itself may panic before the Epoch / above the upper bound. Do not hide this behind a false bounded type invariant or application `trusted` declaration. Count unresolved refinements explicitly as open.
- Trait method refinements are part of coverage. Inspect generated impls, laws, helper goals, and calls without contracts. Even with zero goals, a missing Clone contract does not prove clone semantics. Give it a meaningful postcondition such as exact-copy and inspect the target VC.
- To use an opaque child grammar in a caller proof, the child must pass bounds and uniqueness / extensionality through a checked contract. Do not bridge implementation and contract using only a parent proof assertion.
- Rust array indexing can produce a VC without a contract, even for an index in the full array range `0..N`. If needed, include the whole-array reference and element relationship in the contract so individual array elements can be used safely.
- In Creusot 0.13, `@` on a ghost string literal or a runtime byte-string literal can trigger an ICE / backend `Bytes` todo. Save a minimal reproduction; try explicit scalar byte values in common runtime code and numeric byte predicates for ghost grammars.
- Check whether array conversion or parser extraction has been marked `trusted` to bypass a contract. Restrict external specifications to standard-library boundaries and record their domain and properties not guaranteed on failure in the ledger.
- When a generic trait call automatically dispatches to a reference type, do not confuse external models for different types. Check the actual callee type and precondition in Coma; if needed, make the intended implementation explicit with `<H as Trait>::method(&*value)`.
- Do not model every Hasher implementation with a common append-only trace; legal implementations may ignore `write`. Separate the target domain with deterministic, non-panicking operations, complete internal state, typed transitions, and `finish`. State compatibility for equal values under the same type and initial state. Connect the domain's non-emptiness with a concrete constructor.
- When a model narrows an external API's generic bound, ledger that it does not guarantee the original API for all inputs. Check whether Creusot enforces the added bound at call sites, or use a negative probe with an input legal for the original API that does not meet the added bound. Distinguish a model that preserves a type-erased payload from verification of observer implementations such as downcast.
- When replacing derived Debug, check hex, width, precision, alignment, fill, sign, zero-padding, and nested indentation as well as alternate formatting. If the content contract is limited, state the domain and preserve existing behavior for other formatting options. Compare with recording/failing sinks to ensure the writer call order on Err does not change.
- Inlining a large character mapping into a `Seq::create` lambda can expand the same branches repeatedly in SMT. Check the growth in actual prover input; consider an open/non-inline model that preserves definitions, an extensional equality bridge for the actual array, or splitting into checked write units. Match prover parallelism to the cgroup CPU quota to avoid timeouts from concurrent old diagnostics.
