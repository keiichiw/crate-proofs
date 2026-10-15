# Verification coverage

The fresh macOS arm64 run completed on **2026-10-15 at 05:20:31 UTC**. Its immutable [manifest](evidence/httpdate-run-Nh8aCaki/manifest.json) records the exact targets, generated Coma and proof-session hashes, 51 input fingerprints, and tool identities. The fresh run was `verif/httpdate-run-Nh8aCaki/`; the command was `bash httpdate/1.0.3/scripts/verify.sh`. The independent [archive audit](evidence/httpdate-run-Nh8aCaki/independent-audit.json) passed, including root reconstruction and complete generated-inventory comparison.

The runner uses a fingerprinted version-local Why3 configuration with Z3, Alt-Ergo, and CVC5. CVC5 per-query time limits avoid the macOS exit stall seen with its global timer; CVC4 is disabled. No contract was weakened and no application assumption was added. Earlier unsuccessful attempts remain diagnostic runs; the previous successful bundle is preserved in [historical-ym5gzimb](evidence/historical-ym5gzimb/manifest.json). The latest pointer and this immutable bundle have identical manifests.

## Formal proof in the fresh run

The manifest resolves 268 root goals across 64 selected targets. The generated inventory has 66 items: 64 positive targets, one separately classified expected-open trait refinement, and one excluded generated target. The 268 count is the total for the closed selected root goals. The one expected-open goal and excluded target are not counted as successes.

| Group | Selected targets | Closed root goals | Scope |
| --- | ---: | ---: | --- |
| Shared parser / calendar core | 21 | 111 | Digits, IMF / RFC850 / asctime raw parsers, encoding laws, calendar, formatter kernel, three-format parser kernel, and helper lemmas |
| Public bodies, bridges, and selected refinements | 23 | 68 | Parse / format wrappers, raw/public bridge, FromStr, Display bodies, timestamp conversion, Eq / Ord / PartialOrd / Clone bodies and refinements, trim / bytes uniqueness lemma |
| Hash bodies, refinement, and compatibility harnesses | 4 | 12 | Exact typed fields / order; Eq compatibility for the same H and equal initial state; concrete DefaultHasher witness |
| Error methods, IO body / refinement, and kind observer | 6 | 11 | `source` / `cause` None; exact deprecated description; Other kind and retained concrete payload |
| Public Debug bodies and checked formatting helpers | 10 | 66 | Normal / pretty content under plain options and append sink; ASCII, decimal, prefix, field, and concatenation helpers |

Fresh Coma was used for every selected target. Why3 reconstruction enumerated root goals and confirmed an exact match with proof.json. Each target's proof.json, Coma, and open / excluded inventory are in the manifest and `evidence/latest/`. Success applies only to this selected surface and does not mean the whole crate's public API is proved.

Eleven corruption guards also completed against the fresh manifest. All 11 cases were rejected by the checker, including changed input, zero / missing goals, missing / extra generated targets, changed expected-open classification, and abnormal exit. None changed the latest evidence. Machine-readable results are in [the archived guard results](evidence/httpdate-run-Nh8aCaki/evidence-guards.json).

## Selected contracts and boundaries

- **Raw parsing / validation:** `RawDate` is a permissive record for raw parsers. The syntax and seven-field correspondence of the IMF, RFC850, and asctime raw parsers, plus their safety, are proved. `parse_date_bytes` preserves parser order and succeeds only after calendar validation. Its Err contract states for all three formats that if a corresponding raw encoding exists, that date is calendar-invalid. The checked RFC850 / asctime `encoding_laws` pass grammar length and uniqueness for the record corresponding to the same input. Byte 9 between RFC850 year and time remains unchecked, matching upstream.
- **Public parsing:** Method bodies for `FromStr` and `parse_http_date` guarantee that the input encoding after ASCII trimming corresponds to a valid calendar date and timestamp. On error, they state the relation to calendar validity for encodings in all three formats. The trim / byte bridges use checked uniqueness lemmas.
- **Formatting:** `fmt_http_date` truncates subsecond precision for bounded supported `SystemTime` values and returns a valid date and canonical 29-character IMF content. Content postconditions for `Display for HttpDate` and `Display for Error` hold only when the result is `Ok(())` and `append_sink` is true. There is no guarantee for arbitrary sinks, partial writes on `Err`, or initial formatter output.
- **Public record / traits:** The `HttpDate` invariant is `valid_calendar`. The `Eq` body and timestamp refinement use checked `valid_datetime_injective` to preserve seven-field equality. `Ord` uses shared `to_unix_seconds`; `PartialOrd` returns that result in `Some`. Clone for `HttpDate` / `RawDate` has an exact-copy postcondition. These selected method bodies and refinements closed in the fresh run.
- **Time conversion:** The bounded `From<SystemTime> for HttpDate` body and the reverse `From<HttpDate> for SystemTime` body / refinement were proved. The former's trait refinement is separately classified as one open goal. The unconditional From-trait precondition cannot establish the supported range, and native code panics before the Epoch and from year 10000 onward. The body proof does not close this unconditional refinement. The `system_time_roundtrip` harness has a whole-second floor postcondition; all three of its goals closed in this fresh run.

These public-boundary proofs conditionally depend on [41 standard-library boundary assumptions](stdlib-assumptions.md). They target reviewed 64-bit Linux or macOS arm64 and the supported date range, and include the SystemTime model and Formatter append-sink condition. They are not proofs of the Rust standard-library implementation. Do not extend proofs of the `FromStr` / `Display` method bodies into claims about all external trait-interface contracts. Unselected inherited / specialized default methods are unverified.

## Open / excluded generated targets

The expected-open target is the one goal in `date/impl_From_for_HttpDate/from__refines`, `Coma.refines`. It is the unconditional trait refinement described above, separate from the bounded `From<SystemTime> for HttpDate` body.

The manifest's excluded generated target is the single `date/impl_Debug_for_RawDate/fmt` item for private diagnostics. The two public HttpDate / Error Debug bodies and eight shared helpers, ten selected targets total, all closed in the fresh run.

The four selected Hash targets guarantee the original seven-field typed dispatch, trait refinement, Eq compatibility, and a DefaultHasher witness. They assume the same H and complete initial model state, plus the `supported_hasher` condition of deterministic, non-panicking operations. Formal guarantees do not include collision freedom, digest equality across different seeds or Rust versions, arbitrary Hashers, or `hash_slice` operation sequences. Debug conditionally guarantees normal / pretty content. Error's three stable methods and IO conversion are in the selected scope and depend on a direct-payload-retention model for the standard constructor. Observers using `get_ref` / downcast / `into_inner` have native regression coverage only and are not formally guaranteed. Public `proofs.rs` / SARIF registration has not been recorded or published.

## Native tests and upstream comparison

The fresh runner's `cargo test --locked --release -p httpdate` result was **34 passed, 0 failed, 0 ignored**. The log is [tests.log](evidence/httpdate-run-Nh8aCaki/tests.log). New regressions include public Eq / Ord / PartialOrd, native comparison for Hash / Debug, boundary / subsecond formatter comparisons, Error message / IO kind, and custom `fmt::Write` sinks that succeed or fail. Debug comparisons against upstream include width / precision / hex and other options, nested formatting, and the results and call sequence of a writer that fails at each write position.

Native tests use valid public `HttpDate` values and compare behavior over a finite set of inputs. Agreement with the saved upstream reference is not a formal equivalence proof for all times and inputs. Records of comparing a representative time on every supported civil day are native regression evidence and do not add to formal proof goal counts.

After separating native execution from formal binding, the fresh [native correspondence bundle](correspondence/evidence/correspondence-qZmQ5PXk/manifest.json) is bound to this formal manifest. It passed comparisons over 2,932,897 civil days, 42 boundary instants, 132,353 parser inputs, 8,868 trait pairs, 90 formatting observations, 2,560 writer observations, eight panic observations, and one Error observation. This run checked the saved reference sources against their captured release record; it did not fetch a new registry response or reauthenticate the release archive. These finite observations do not establish formal upstream equivalence.

## History of the independent trial

Proofs for the shared core and the independent method trial associated with the earlier `7c1dcef` remain in [`trial/method.md`](trial/method.md) and the related trial evidence, as results for their historical scope and assumptions. Do not add goals from the earlier coverage, boundary model, or three-field trait model to the current total of 268. See the [assumptions ledger](stdlib-assumptions.md) for the conditional standard-library boundary currently used in production, and distinguish standalone experiment native checks from production formal proofs.

## Debug guarantee conditions

The model guarantees the exact seven field names, order, and decimal values of public `HttpDate`, and `Error(())` / pretty Error output. It applies only when the result is Ok, `append_sink` is true on entry, flags are 0 or 4, width / precision / alignment are `None`, and fill is a space. Under standard-library boundary assumptions that preserve formatter options and the sink condition, checked helpers combine small writes into the complete output. The pretty-mode decimal helper preserves the standard PadAdapter behavior that omits empty writes. Native comparisons with failing writers are finite regression evidence.

Other format options call the standard builder and preserve native behavior, but have no formal content guarantee. There is no guarantee for partial output on `Err` or for output through a transforming / indenting sink. The initial output is not assumed empty. This is a proof of postconditions for the selected method bodies, not a claim that the entire standard Debug trait interface is refined. The standard-library implementation itself is unverified. Remaining gaps include the open unconditional `From<SystemTime>` refinement, the default Hash slice operation sequence, dynamic Error observers, and public proofs.rs / SARIF registration.
