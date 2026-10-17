# Verification results: form_urlencoded 1.2.2

The standard Why3find run completed on 2026-10-17 UTC. Its immutable bundle is
[form-urlencoded-etJOlOat](evidence/form-urlencoded-etJOlOat/manifest.json), also
selected by `evidence/latest`. The [independent audit](evidence/form-urlencoded-etJOlOat/audit.log)
reconstructed the original root goals from saved Coma and checked the complete
generated inventory against current inputs.

## Formal result

All **159 original root goals across 88 selected targets** closed. All 89 generated
targets were classified; derived `ByteSerialize::Debug::fmt` remains excluded.
The scope comprises parsing and owned parsing, exact iterator traces/state/clone/
size hints, byte serialization, and concrete `Target` implementations for `String`
and `&mut String`, including body/refinement/law obligations. Exact guarantees and
boundaries remain in [coverage](coverage.md), [API inventory](public-api-inventory.md),
and [assumptions](assumptions.md).

Creusot 0.13 freshly generated Coma with absolute source spans. Standard Why3find
ran with Z3 and CVC5, `--no-cache -f`, and recorded genuine `proof.json` trees.
There was **no custom SMT editing or assumption-removal fallback**. No Rust runtime
code, contracts, or application assumptions changed for this transition.

The run pinned 283 input files and 13 tool binaries; before/after fingerprints
matched. The version-local Why3 configuration uses CVC5's per-query timeout.
The host is `aarch64-apple-darwin`. Manifest SHA-256:
`7e9efe7807c704fe2bdbc18da585051dcf479c112dc6ffe682f771168ae2a153`.
Native and formal compilation use new target directories, avoiding replay of
cached timestamped diagnostics. Compilation/prover logs, successful prover exit, tool versions, native logs,
source/model/configuration/driver hashes, and sessions are saved in the bundle.

## Separate native evidence

The source-matched immutable-release differential comparison passed for 85,542
inputs, including malformed escapes and UTF-8, Cow variants, owned parsing,
and intermediate clones. It checked 394,459 size-hint observations and one
Serializer chain case. See [differential.log](evidence/form-urlencoded-etJOlOat/differential.log).

All-features native testing passed one doctest (no unit tests are defined), and
the no-default-features `alloc` build passed. Their logs and hashes are saved
separately as [tests.log](evidence/form-urlencoded-etJOlOat/tests.log) and
[check-alloc.log](evidence/form-urlencoded-etJOlOat/check-alloc.log).
Finite native observations do not establish universal upstream equivalence.

## Exclusions and reproduction

Serializer and EncodingOverride remain unverified because Creusot 0.13 rejects
the actual dynamic callback type. Derived Debug rendering, individual standard-
library iterator default bodies, arbitrary caller implementations, pointer/
allocation identity, OOM, and all-platform behavior remain outside the guarantees.
This proves the selected fork contracts under the recorded library models, not
the standard library or equivalence to the unmodified crates.io release.

From the repository root, using Bash 4 or newer:

```bash
source scripts/activate.sh
bash form_urlencoded/1.2.2/scripts/verify.sh
python3 scripts/audit-proof-evidence.py form_urlencoded/1.2.2 \
  --manifest form_urlencoded/1.2.2/verification/evidence/latest/manifest.json \
  --reconstruct-root-goals
```

Why3find needs local why3server socket communication. The initial sandboxed
attempt did not progress; the successful run used an environment permitting
that local communication. No external service or publication was involved.

## Historical evidence

Earlier uncommitted standard runs are preserved locally under ignored
`verif/precommit-history/`; their old execution logs are not part of the current
commit proposal. The direct
bundles [direct-s8YxnYN7](evidence/direct-s8YxnYN7/manifest.json), `direct-eXUoE5EK`,
`direct-ncQF3RwB`, and the byte-core milestone remain unchanged evidence for their
own frozen inputs. `latest-direct` retains its historical direct-SMT meaning.
This post-run status page is excluded from proof-input fingerprinting.

No cargo-proofs SARIF recording or proofs.rs publication has been performed.
