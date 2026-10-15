# percent-encoding 2.3.2 verification results

The fresh macOS arm64 run completed on 2026-10-15 UTC after the standalone native-runner and dependency-evidence updates. Its immutable bundle is [percent-encoding-5hAvcajG](evidence/percent-encoding-5hAvcajG/manifest.json), also selected by `evidence/latest`. The [independent archive audit](evidence/percent-encoding-5hAvcajG/independent-audit.json) checked the current inputs and the complete generated inventory. Earlier archives remain evidence only for their own frozen inputs.

## Current audited full-scope result

- **122 generated targets completely classified: 121 selected, zero open,
  one excluded compile-time `ascii_set/static_assert`.**
- **305/305 positive original root goals closed.**
- **1,182/1,182 original exported SMT leaves returned UNSAT:** 1,169 with Z3,
  13 with CVC5 after Z3 timeout/unknown. CVC5 checked the identical original SMT
  input; no assumptions or assertions were removed.
- In-place audit, copied-archive audit, and the primary agent's independent
  archive audit all passed. The final build used fresh Coma and Cargo target
  directories, with locked offline dependency resolution.
- **12,329 input-file hashes and nine tool-binary hashes were pinned**;
  before/after source and tool fingerprints matched. Native fingerprints also
  match the proof-run input snapshot.
- Manifest SHA-256:
  `1012051ef7cea2e1f9193616cfd1dbb56d39518d1929af65b8be79268343d4f7`.

There are no application `trusted` declarations or new application assumptions.
The standard-library implementation/model boundaries are assumed correct as
authorized by the user; their precise contracts are in [assumptions.md](assumptions.md).
This is closure of the stated verification conditions, not a proof that the
chosen external models capture every possible property.

## Verified behavior

The complete per-API inventory is in
[public-api-inventory.md](public-api-inventory.md). The integrated proof covers:

- Exact uppercase `%HH` encoding for all 256 byte values, including `%20` for
  space; configured encoding constructors preserve input and mask.
- Exact four-word ASCII-set constants, membership/encoding decisions, union,
  complement, equality, and one-bit add/remove under `byte < 128`.
- Encoder maximal-safe-run/escaped-byte chunks and decoder exact `%HH` steps.
  Malformed or truncated escapes retain the leading byte literally; `+` is
  retained. Both iterator production relations, completion, trait refinements,
  production laws, and size-hint bounds are checked.
- Clone preserves the current remaining state; encoder equality compares
  remaining raw bytes and the configured mask. A checked integer-model to
  byte-view extensionality bridge supports this equality guarantee.
- Encoder and decoder Cow content and their specified borrowed/owned branch
  conditions. Encoder content is tied to UTF-8 bytes of flattened chunks.
- Strict UTF-8 success contents/ownership and the observed error fields
  `valid_up_to` and `error_len`; lossy contents/ownership compose with the
  inherited standard-library lossy conversion contract.
- Display requested chunk order and stopping/propagating the first formatter
  error. Debug struct names, ordered field names, typed supplied values, and
  returned finish status are checked as request traces.

All supporting emitted helper, refinement, and law targets are included. The
excluded `static_assert` target binds internal function items for compile-time
constant assertions; it executes no codec algorithm. Native compiler checking
of those assertions remains enabled.

## Verified dependency chain

The run freshly audited the pinned `form_urlencoded 1.2.2` evidence
`direct-s8YxnYN7` (88 selected targets, 159 original roots) and checks actual
uses of its checked contracts in generated Coma. Encoding-array/hexadecimal
and byte-sequence/subsequence bridges are reused; percent-encoding supplies
its own checked decoder trace and its own `%20` behavior. No claim is made
that form's plus-to-space decoder is the same algorithm.

The local form-model path dependency retains its own registry percent-encoding
dependency, avoiding a Cargo or logical dependency cycle. Exact identities and
limits are in [dependency-ledger.md](dependency-ledger.md).

## Separate native evidence

The final source-matched native run passed with ID
`percent-encoding-2.3.2-full-scope-20261015T143910Z-19511`.
All seven logs and the harness JSON have this ID; all 30 fingerprint rows,
including eight immutable capture files, match before/after and the proof
snapshot. See [differential/README.md](differential/README.md).

The differential corpus contains **65,945 inputs**: every singleton byte and
all 65,536 two-byte sequences, 129 deterministic inputs, and 24 targeted
percent/UTF-8 cases. Seven encoding sets yield 461,615 encoding cases. Checks
include 892,191 chunks, 1,784,382 encoder equality observations, 205,604 Cow
observations, 411,208 strict/lossy UTF-8 results, six forced-owned invalid UTF-8
error values, and 3,118,834 Debug text comparisons. Failing Display/Debug sinks
also match on the finite tested request traces.

Fork and staged-upstream tests each passed 18 unit tests and six doctests;
the fork's separate six-doctest run and default, bare, and alloc-only builds
passed. These finite native results are separate from formal proofs and do
not establish all-input equivalence with the upstream release.

## Limits and reproduction

The result covers crate-owned public implementations within the explicit
models. It does not prove rendered Display/Debug text or arbitrary sink effects,
allocation/capacity/pointer identity/OOM, out-of-domain ASCII indexing behavior,
or individual instantiations of inherited standard-library default methods
(including Iterator defaults, `PartialEq::ne`, and `Clone::clone_from`).
It also does not establish upstream MSRV compatibility or all-platform behavior.
The proof is for the adapted verification fork, not universal source-equivalence
with the immutable upstream capture.

The former 21-target archive `percent-encoding-v49MYwzO` is historical; the
incomplete final attempt `percent-encoding-s43DOmha` is diagnostic evidence only
and was not published as passing. The archived integrated run includes the checked
sequence bridges that closed its three remaining obligations.

To reproduce from the repository root after regenerating matching native logs:

```sh
source scripts/activate.sh
bash percent-encoding/2.3.2/verification/differential/run-full-scope.sh
bash percent-encoding/2.3.2/scripts/verify.sh
```

This post-run report is deliberately excluded from the input fingerprint;
source, scope documents, scripts, and evidence remain frozen. Historical bundles, including `percent-encoding-jIA5xCX8` and `percent-encoding-J4mz7h2U`, remain unchanged. Nothing has been submitted or published.
