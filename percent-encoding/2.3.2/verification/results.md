# percent-encoding 2.3.2 verification results

The standard Why3find run completed on 2026-10-17 UTC. Its immutable bundle is
[why3find-wQmj7m3T](evidence/why3find-wQmj7m3T/manifest.json), also selected by
`evidence/latest-why3find`. Both the [in-place audit](evidence/why3find-wQmj7m3T/audit.json)
and the [copied-archive audit](evidence/why3find-wQmj7m3T/archive-audit.json) passed.
The in-place audit checked the complete generated inventory; both reconstructed
original root goals from saved Coma and matched current proof inputs.

## Current formal result

- **122 generated targets completely classified: 121 selected, zero open,
  one excluded compile-time `ascii_set/static_assert`.**
- **305/305 positive original root goals closed.**
- Creusot 0.13 freshly generated Coma with absolute source spans, using a unique
  Cargo target directory and locked offline dependencies.
- Standard Why3find, with Z3/CVC5 and `--no-cache -f`, generated genuine
  `proof.json` trees. No custom SMT editing, assumption removal, or synthesized
  proof results were used.
- **12,333 input-file hashes and 10 tool-binary hashes** were recorded;
  before/after fingerprints matched. The native run's 30 source/configuration
  fingerprint rows also match the proof input snapshot.
- Manifest SHA-256:
  `1c089001754f761a349d5d48838f04bc018b26deeb5ff1cfd4edba62e2e7e947`.

The host is `aarch64-apple-darwin`. The version-local Why3 configuration uses
CVC5's per-query timeout. Proof search, transformation, solver selection, and
proof-tree recording are performed by standard Why3find/Why3. The surrounding
scripts select targets, preserve fingerprints/logs, and audit the results.
No Rust runtime code, contracts, or application assumptions changed for this
transition. Standard-library model assumptions remain in [assumptions.md](assumptions.md).

## Verified behavior

The [public API inventory](public-api-inventory.md) and [specification](specification.md)
define the guarantees, including uppercase `%HH` encoding, exact ASCII-set
operations, encoding/decoding traces and iterator laws/refinements, state clone/
equality, size hints, Cow content and branch conditions, strict UTF-8 result and
error observers, lossy UTF-8 contents, and Display/Debug request traces.

All selected supporting helper, refinement, and law targets are included.
The excluded `static_assert` binds internal function items for compile-time
constant assertions; native compiler checking remains enabled.

## Verified dependency chain

The run freshly audited the pinned standard form_urlencoded bundle
[form-urlencoded-etJOlOat](../../../form_urlencoded/1.2.2/verification/evidence/form-urlencoded-etJOlOat/manifest.json),
covering 88 selected targets and 159 original roots. The package checks generated
Coma for the checked `encoded_array_model` and `byte_model_subsequence` dependency
calls. Exact source identity and evidence hash are in [dependency-ledger.md](dependency-ledger.md).

The local `form-model` alias retains its own registry percent-encoding dependency,
avoiding a Cargo or logical dependency cycle. Form's plus-to-space semantics are
not assumed to be percent-encoding's decoding semantics.

## Separate native evidence

The source-matched native run passed with ID
`percent-encoding-2.3.2-full-scope-20261017T030514Z-37273`.
All seven logs and the source fingerprint are preserved under the bundle's
`native-evidence/`, with hashes in the manifest.

The differential corpus contains **65,945 inputs**, including every singleton
byte, every two-byte sequence, deterministic inputs, and directed percent/UTF-8
cases. Seven sets yield 461,615 encoding cases. Observations include 892,191
chunks, 1,784,382 encoder equality checks, 205,604 Cow observations, 411,208
strict/lossy UTF-8 results, six forced-owned invalid UTF-8 error values, and
3,118,834 Debug text comparisons. Failing Display/Debug sinks also match on the
finite tested request traces.

Fork and staged-upstream tests each passed 18 unit tests and six doctests;
the separate fork doctest run and default, bare, and alloc-only builds passed.
These finite native observations are separate from formal proof and do not
establish all-input equivalence to the upstream release.

## Limits and reproduction

The result covers crate-owned implementations within explicit models. It does
not prove rendered Display/Debug text or arbitrary sink effects, allocation/
capacity/pointer identity/OOM, out-of-domain ASCII indexing, individual inherited
standard-library default methods, upstream MSRV, or all-platform behavior.
The proof is for the verification fork, not universal source equivalence with
the immutable upstream capture.

From the repository root, using Bash 4 or newer and allowing Why3find's local
why3server socket communication:

```sh
source scripts/activate.sh
bash percent-encoding/2.3.2/scripts/verify-why3find.sh
```

The standard runner first regenerates native evidence using a fresh Cargo target
directory, then uses the immutable form evidence pin. If dependency proof
inputs change, regenerate and audit form first, then update the dependency pin
before freezing and proving percent-encoding.

The former direct-SMT bundle `percent-encoding-5hAvcajG`, still selected by the
historical `evidence/latest`, and earlier bundles remain unchanged evidence for
their own frozen inputs. `scripts/verify.sh` is the historical direct runner;
the current standard runner is `scripts/verify-why3find.sh`.
The first refresh attempt (`why3find-WA9rOLiu`) stopped during Z3 calibration
with a timeout. The successful run above repeated native checks and the full
proof pipeline without changing contracts or solver settings. Failed and older
uncommitted execution bundles remain local under ignored `verif/` directories.
This post-run status page is excluded from proof-input fingerprinting.

No cargo-proofs SARIF recording or proofs.rs publication has been performed.
