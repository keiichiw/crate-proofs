# Verification method selected in the 2–4 hour trial

This document records the method trial through commit `7c1dcef`. Follow-up work adopted the boundary model in the main crate, and added public adapters and the actual comparison traits. For the current proof scope, conditions, and open issues, see [coverage](../coverage.md), the [specification](../specification.md), the [assumptions ledger](../stdlib-assumptions.md), and the latest manifest.

The trial started at 2026-10-07 18:29:10 UTC. Its end time and actual run results are recorded in [summary.json](summary.json); the latest main evidence is in [../evidence/latest/manifest.json](../evidence/latest/manifest.json). The organization commit is `1a71594`. The trial aimed to choose a practical method for implementation, specification, and evidence capture while advancing verification of the public API.

## Adopted structure

**First close and prove the native-shared byte / integer core; then connect the standard-library boundary outside it under explicit specifications.** Do not trust the algorithm, and preserve upstream computation and acceptance behavior as far as possible. We did not adopt a method that checks the pure core only through an independent reimplementation.

Calendar calculations, integer conversion, 29-byte output, all three raw parsers, validity checks, and the common parser kernel are shared by native code and Creusot. Contracts were added in stages for digit conversion, Gregorian dates including real month lengths and weekdays, round trips, successful content of all three formats, and IMF acceptance. Before counting an overall success, prove the contracts of each called application-level function and lemma.

This makes it possible to investigate missing standard-library specifications separately from algorithm proof complexity. While public wrappers are excluded from the Creusot configuration, do not call them a verified public API.

## Findings from the experiments

| Experiment | Result and decision |
| --- | --- |
| Shared calendar core | Adding intermediate relations and loop invariants to the March-based 400-year cycle calculation makes it possible to prove Gregorian day numbers, actual month lengths, and weekdays. Second / calendar round trips and the validator can also be closed. |
| Raw byte parser / formatter | Put input length, separators, digits, names, and the correspondence to seven fields in separate ghost functions. Byte-string patterns have translation issues in 0.13, so use scalar byte comparisons. |
| Parser composition | `Result::or_else` had no usable contract and became a barrier. An explicit `match` preserves the same short-circuit order and allows the shared kernel to be verified. `Option::or_else` worked for RFC850 weekday selection. |
| Bounded proof search | Instead of running deep automatic search for a long time, inspect the actual prover input for the failed VC and add the needed contract / cut. Use fresh output, depth 2, and `--no-cache`; 120 seconds was the usual upper bound for difficult trials. The cut itself must also be proved. |
| Duration | Existing creusot-std models were sufficient to prove the relationship between seconds and nanoseconds. |
| SystemTime / str | The original calls translated, but could not be proved because required external specifications were missing. In an independent boundary-model experiment, five targets were proved conditionally after adding reviewed, limited external specifications. |
| Eq / Ord | Deriving the traits alone, or leaving methods without contracts, did not prove caller-visible meaning. A small model with structural DeepModel and explicit comparison contracts was closed, including generated implementations, laws, and refinements. |
| Formatter / Hash / I/O Error | Formatter calls translated and proofs under existing contracts succeeded, but there was no output-string contract. Hash / I/O Error lacked required specifications. These were not counted as proofs of public API semantics. |

Detailed standard-library experiments are in [probe-results/summary.json](probe-results/summary.json); failed trait experiments are in [trait-probe-results/summary.json](trait-probe-results/summary.json), and successful independent models are in [trait-model-results/summary.json](trait-model-results/summary.json). A probe runner exiting successfully means it recorded the expected failure; it does not mean the target was proved. The main runner requires every target to be proved.

## Standard-library trust boundary

The review of additional external specifications is in [boundary-model/README.md](boundary-model/README.md). It documents eight items: `time_ns`, `UNIX_EPOCH`, `duration_since`, limited Epoch addition, and ASCII UTF-8 conversion, `is_ascii`, `trim`, and `as_bytes`. The Rust nightly source commit, reference URLs, and SHA-256 hashes were saved. Scope is limited to 64-bit Linux and the supported HTTP date range.

Proofs with this model are **conditional results that trust those external specifications**. They are not proofs of the standard-library implementation or the main crate's public API. Native sanity tests help find specification mistakes; they are not formal proofs of the specifications themselves. In particular, ASCII `str::trim` removes bytes 9..13 and 32, so it cannot be equated with byte `is_ascii_whitespace`, which excludes vertical tab.

Formatter output / String allocation, behavior of a user-supplied Hasher, and `io::Error` require additional semantic models. Do not claim unconditional absence of panics for traits that call user code.

## Separate implementation behavior from the standard

The RFC850 parser does not check the byte between the year and time, and accepts `Sunday, 06-Nov-94x08:49:37 GMT`. The two-digit-year pivot is also fixed at 70. The trial preserved upstream behavior and recorded this acceptance in the contract and native test. To verify conformance to the standard, define that specification separately and address any difference from upstream.

The `HttpDate` returned by a raw parser may contain an invalid calendar date. The then-current `Eq` compared all seven fields; `Ord` compared six fields excluding weekday. Adding a type invariant that “all HttpDate values are valid” as-is would conflict with the raw parser. The next stage was to **separate `RawDate` from validated `HttpDate` and guarantee a calendar invariant, including weekday, only for public values**. Then prove the actual seven-field Eq / Ord laws. Success in an independent three-field model showed only that this design was feasible.

Public conversions panic before the Epoch and from year 10000 onward, and truncate nanoseconds. Specify normal-domain preconditions, existing panics, and precision separately. Do not mix possible panics in a formatter writer / Hasher with the safety of an unrelated algorithm.

## Saving reproducible evidence

The main crate uses `bash httpdate/1.0.3/scripts/verify.sh`. After native release tests, it cleans the target package's Creusot build and generates Coma in a new `verif/httpdate-run-*/`. This clean was necessary because Cargo did not regenerate output just because the output directory changed.

Compare fingerprints for all source, contracts, lockfile, fixed upstream reference, toolchain, configuration, and run scripts at the start and end of execution. Check for the target VC, a nonzero goal count, and every leaf in the proof tree before saving Coma, proof.json, logs, and manifest into tracked evidence. Include callees and generated closures / trait laws. Do not accept results produced while another agent edits shared source. The trial detected input changes and rejected attempts to update evidence with stale results.

Do not infer the runtime failure location from failed proof-tree node numbers or branch labels such as “Jun” in an expanded postcondition. For RFC850, extracting the actual timeout prover input from the saved session showed that rejection of the weekday Option chain was the cause, not year parsing or month selection. Adding `!prefix.ext_eq(name)` to the helper's rejection contract, and proving that contract, connected slice mismatch to the bytewise grammar and resolved the problem without weakening the strong contract. Adding the bytewise extensionality rejection contract to the slice helper closed both helper and caller. Commands and the fix are recorded in the [diagnostic procedure](rfc850-diagnostic.md). Inspect actual assumptions and goals before adding cuts based on an ambiguous location guess.

The upstream `date.rs` was saved unchanged as a reference implementation. Native tests compare a representative time, 12:34:56, for all 2,932,897 days, along with boundaries, invalid dates, all byte digit conversions, and replacement inputs to the legacy parser. Do not call this finite execution comparison an equivalence proof for all seconds and inputs.

Keep general process in the top-level skill and crate-specific contracts, regression tests, and results in `httpdate/1.0.3/`. Luna handled routine scaffolding, probes, and documentation; Astra was consulted on difficult calendar proofs and blocked VCs. Primary reviewed contracts and trust boundaries and performed final integration. Per-model token consumption is unavailable, so do not present estimates as measured values.

## Next steps recorded at the time

1. Strong contracts for all three raw parsers are proved. Next, add complete content and acceptance specifications for the shared parser kernel, including RFC850 / asctime. At that time, the kernel's explicit acceptance and content guarantee covered IMF only. Specify the entire priority-ordered public parser separately.
2. Organize the type boundary between `RawDate` and valid public `HttpDate`, and connect the actual Eq / Ord to the method that succeeded in the independent model.
3. Adopt the reviewed standard-library boundary specifications in the main crate and close the `From<SystemTime>`, `Into<SystemTime>`, and `FromStr` wrappers and public parse. Check the domain of every affected call.
4. Develop Formatter / String models for output content and connect `Display` / `fmt_http_date`. Define the semantic contracts needed for Hash / Debug / Error separately. For Hash, use an abstract input sequence and callback contract; do not claim a fixed hash value.
5. Record cargo-proofs once public API proofs are available. Do not treat the current private core as a count of registered public APIs.

cargo-proofs requires public annotated APIs, a clean committed tree, Cargo.lock, and a source commit reachable on GitHub. Record method evidence with output that identifies relative spans when mapping it to source. The local core runner in this trial uses `span-mode off`. Check SARIF registration of `panic_contract` separately from the functional postcondition proofs described here. No login, push, or publish was performed in this trial.
