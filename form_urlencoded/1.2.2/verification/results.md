# Verification results: form_urlencoded 1.2.2

The fresh macOS arm64 run completed on 2026-10-15 UTC after the standalone native-runner portability changes. Its immutable bundle is [direct-s8YxnYN7](evidence/direct-s8YxnYN7/manifest.json), also selected by `evidence/latest-direct`. The independent [archive audit](evidence/direct-s8YxnYN7/audit.log) passed against the current inputs. The run recorded 285 input files and checked unchanged source/tool fingerprints before and after execution.

## Formal result

All **159 original root goals across 88 selected targets** closed. All 89 generated targets were classified, with the derived `ByteSerialize::Debug::fmt` target excluded. The scope comprises parsing and owned parsing, exact iterator traces/state/clone/size hints, byte serialization, and the concrete `Target` implementations for `String` and `&mut String`, including body/refinement/law obligations. See [coverage](coverage.md), [API inventory](public-api-inventory.md), and [assumptions](assumptions.md) for exact guarantees and boundaries.

Why3 freshly exported 1,456 original SMT leaves. Z3 returned UNSAT directly for 1,450. Six original timeouts closed through the existing checked removal of selected original assumptions; the reduced tasks retain the original goals, so their UNSAT results entail the original obligations. The original timeout results are preserved, not relabeled. The bundle contains 1,462 SMT files including those six reductions. No Why3find `proof.json` is claimed for this direct-SMT workflow.

The native host is `aarch64-apple-darwin`; the manifest records the compiler identity and tool hashes. This is proof of the selected fork contracts under the recorded standard-library models, not a proof of the standard library, all platforms, or equivalence to the unmodified crates.io release. No application algorithm was changed or made trusted by this refresh.

## Separate native evidence

The fresh immutable-release differential comparison passed for 85,542 inputs, including malformed escapes and UTF-8 cases, Cow variants, owned parsing, and intermediate clones. It checked 394,459 size-hint observations and one Serializer chain case. [Differential log](evidence/direct-s8YxnYN7/differential.log).

The all-features native test command passed its one doctest (no unit tests were defined), and the no-default-features `alloc` build passed. Their logs are [tests.log](evidence/direct-s8YxnYN7/tests.log) and [check-alloc.log](evidence/direct-s8YxnYN7/check-alloc.log); their hashes are checked by the evidence auditor. These finite observations are separate from formal proof.

## Exclusions and reproduction

Serializer and EncodingOverride remain unverified because Creusot 0.13 rejects the actual dynamic callback type. Derived Debug rendering, individual standard-library iterator default bodies, arbitrary caller implementations, pointer/allocation identity, OOM, and all-platform behavior remain outside the guarantees.

From the repository root:

```bash
source scripts/activate.sh
bash form_urlencoded/1.2.2/scripts/verify-direct.sh --ground-fallback
python3 form_urlencoded/1.2.2/scripts/audit-direct-evidence.py form_urlencoded/1.2.2 \
  --manifest form_urlencoded/1.2.2/verification/evidence/latest-direct/manifest.json
```

Activation selects the isolated native tools on macOS and the recorded cloud tools on Linux. The expanded direct workflow uses `latest-direct`; `latest` remains the historical byte-core pointer.

The previous [direct-eXUoE5EK](evidence/direct-eXUoE5EK/manifest.json), earlier [direct-ncQF3RwB](evidence/direct-ncQF3RwB/manifest.json) and [byte-core milestone](evidence/milestone-1/manifest.json) remain unchanged historical evidence for their own inputs. This post-run report is excluded from proof-input fingerprinting; contracts, scope, assumptions, scripts, and tool inputs remain fingerprinted. Nothing has been submitted or published.
