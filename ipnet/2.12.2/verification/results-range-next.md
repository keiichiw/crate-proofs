# Local verification results — ipnet 2.12.2

Accepted run: **2026-10-16**, [check-X7MRKMCv](runs/check-X7MRKMCv/result.json).
The complete verifier passed with **196 audited theorems: 43 public contracts
and 153 helpers**. The new completion unit is `Ipv4AddrRange::next`, under the
explicit standard-library model correspondences below. This is not whole-crate
verification.

## New range-next guarantees

Astra independently fixed [the specification](range-next-specification.md) and
reviewed the implementation contracts and boundaries. Sol authored the proofs;
the primary reviewed the statements, inventory and reproducible full evidence.

For every raw IPv4 start/end pair, with no ordering or construction-history
precondition, `RangeNext.range_next_spec` proves that the actual extracted
`Iterator::next` body returns normal Aeneas success. In the same theorem, both
the returned option and updated range agree with an independent Nat model:

| Initial remaining interval | Returned value | Updated remaining interval |
| --- | --- | --- |
| Empty (start > end) | None | Empty |
| [s,t), with s+1=t | Some address of value s | Empty |
| [s,t), with s+1<t | Some address of value s | [s+1,t) |

The interpretation of a nonempty inclusive range is [start,end+1). The full IPv4
range therefore has natural-number upper endpoint and length 2^32. Zero and MAX
singletons, reversed endpoints, arbitrary octets and the full range are included.
The equality branch's actual `(1,0)` sentinel is proved empty. In the less-than
branch, non-saturation follows from start < end < 2^32; it is not a new public
assumption.

`constructor_remaining` connects the actual raw constructor to this interpretation.
`RangeLaws` derives None iff Empty, exact returned head, one-element size decrease,
disjoint singleton/residual set partition, empty preservation, a second None after
None, and no revival after any finite sequence of actual next calls. Conditional
result laws use the unconditional total-success body theorem; they do not replace
it with a success-only assumption. The independent RangeMath laws alone do not
count as implementation coverage.

The preceding 158 audited theorem entries and 42 public mappings are retained
unchanged. Their containment, constructor, observer, mask, boundary, truncation,
conversion and raw-constructor scope is recorded in
[the containment results](results-containment-core.md) and
[the arithmetic results](results-arithmetic-core.md). The current 43 contract
mappings cover 40 API forms under the existing convention: containment includes
six specializations of three generic methods. Helper proofs are not extra APIs.

## Explicit semantic trust

The [model ledger](model-boundaries.md) records the exact distinction between
kernel-proved model connections and reviewed Rust/model correspondence. Existing
concrete IPv4/IPv6 octet types and address `Ord::cmp` models remain reviewed trusted
boundaries; this extension does not prove the Rust comparators themselves.
Actual partial_cmp, IPv4 IpStep replacements/increment, IpAdd saturating addition,
constructor and range-next bodies are extracted and composed with these models.

`mem::replace` and U32 saturating addition remain existing Aeneas library models.
The backend patch adds only a kernel-proved exact-min value lemma about the
unchanged saturating-add definition. It introduces no new model algorithm,
axiom, exposure change or new Rust/model correspondence. The proof connects both
returned old value and updated destination from mem::replace. Scalar, byte-order,
Rust-to-LLBC-to-Lean translation, reviewed tool patches and Lean kernel trust
remain explicit. The previous default-le and IPv6 segments/comparator boundaries
are unchanged; see the containment report for their detailed limitations.

## Checks and evidence

- Unchanged release 2.12.2 at 13c5c5873c02127679b1e8e64b538e4e36942640;
  archive checksum 791930b43c0d5973160d90a8f3894509f2b273430f5c5c73b668636d0287c5c0.
  Latest stable release was resolved on 2026-10-16; no upgrade occurred mid-proof.
- Pinned sources, Cargo surface, tools, binaries, exact patches and actual Lake
  dependency verified. Reviewed Rust source hashes and aarch64-apple-darwin,
  little-endian, 64-bit extraction configuration verified.
- Fresh shared extraction byte-identical to maintained generated Lean. The new
  exact standard-trait/local-concrete-type selector extracts actual Iterator::next.
  Generated axioms/incomplete bodies remain forbidden. Compared with the accepted
  containment generation, existing generated lines are unchanged (insertions only).
- Local proof package cleaned, rebuilt and all **196/196** named theorems audited.
  Only propext, Classical.choice and Quot.sound are permitted transitively;
  no sorryAx, application axiom or native-decision axiom accepted.
- Eight kernel-checked shift examples passed.
- Native tests separately passed in both default and no-default-features settings:
  **33 unit + 10 integration + 56 doc tests per setting**. The new test compares
  returned values and exact updated raw states for eight boundary ranges across
  five successive calls. These finite tests do not replace universal proofs.
- Shared helper test suite separately passed: 39 tests run, one skipped.
- Before/after fingerprints match. All recorded artifact hashes and the current
  input fingerprint were independently rechecked after the verifier passed.

The combined Aeneas patch SHA-256 is
097d634787105fab741871cf1f43fee84522e9c69503028e4c3b0d29e0c5b89e.
The Aeneas executable identity remains unchanged. The compatibility patches,
Miri/runtime-check limitations and prior rejected extraction approaches remain
in [extraction-notes.md](extraction-notes.md). This does not claim const-evaluation,
abort/unwind, compiler-equivalence or other-platform correctness.

## Remaining work and bugs

IPv4 next_back/skips/count and other iterator methods, IPv6/enum iterator
transitions, hosts, subnet partition and aggregation union preservation remain
unproved. Raw iterator constructors prove storage only, except for the additional
IPv4 range interpretation connection above. supernet/is_sibling, mask
construction/parsing, other conversions/traits, parsing/formatting, serde/schema
and optional integrations remain outside accepted scope. An empty
extracted-but-unproved inventory is not a whole-crate coverage claim.

No new ipnet bug was found during this range-next continuation. The previously
confirmed schema output-conformance bug and permissive-schema mismatch remain
in [bugs/README.md](bugs/README.md), with standalone reproductions for a later
upstream PR. No issue, PR, login, push, upload or publication occurred.

## Reproduction and immutable run identity

Run `bash ipnet/2.12.2/scripts/verify.sh` from the repository root. Evidence remains
local in the ignored verification/runs directory.

- Complete result SHA-256: 99659fe783a8da70e3c5b515b05357564731a1dd62705ddedd86ca7bb2feb769
- Input fingerprint SHA-256: e723a72111ec42adeaeb66907aa431ac8cf8ce2e7d9cf1306487b5cc7d135703
- Audit result SHA-256: b4cbc874b0587e7fe96ca69aff20ac9c22b1334afa76be1f03ea181ed426700f

The result JSON records artifact/log hashes. This post-run summary is excluded
from the input fingerprint. Prior results are archived in results-initial-core.md,
results-arithmetic-core.md and results-containment-core.md with their original
run identities.
