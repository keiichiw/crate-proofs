# Local verification results — ipnet 2.12.2

Accepted run: **2026-10-16**, [check-bjEjjfsA](runs/check-bjEjjfsA/result.json).
The complete verifier passed with **158 audited theorems: 42 public contracts
and 116 helpers**. The expert's first completion unit, containment, is complete
**under the explicitly reviewed standard-library model correspondences below**.
This is not whole-crate verification or a proof of Rust's address comparators.

## New containment guarantees

Astra independently fixed the [containment specification](contains-specification.md)
and reviewed the final statements and model boundaries; Sol authored the proofs.
The primary reviewed contracts, mappings, LLBC instance identities and the full run.

| Public specialization | Normal-success result is true exactly when |
| --- | --- |
| `Ipv4Net::contains<&Ipv4Addr>` | The address belongs to the receiver's CIDR interval |
| `Ipv6Net::contains<&Ipv6Addr>` | Same, at width 128 |
| `Ipv4Net::contains<&Ipv4Net>` | The operand's represented set is a subset of the receiver's |
| `Ipv6Net::contains<&Ipv6Net>` | Same, at width 128 |
| `IpNet::contains<&IpAddr>` | The tagged address belongs to the receiver's tagged set |
| `IpNet::contains<&IpNet>` | The operand's tagged set is a subset of the receiver's |

The independent model uses network-order octet value a and Nat arithmetic:
K=2^(w-p), lo=(a/K)*K, hi=lo+K-1. Networks require only p≤w; network operands
require the same validity condition. Arbitrary host bits, /0, full-width prefixes,
zero and MAX are included. IPv4 and IPv6 stay disjoint, including IPv4-mapped
IPv6. Both mismatched-family branches return false. Mutual containment is not
asserted to imply equality of the original stored network values.

Six actual trait implementations and six public generic specializations are
proved in `Proofs/Contains.lean`. The public statements fix the corresponding
concrete dictionaries instead of assuming arbitrary trait instances are correct.
Aeneas emits the two IpNet methods but omits their unused dictionary records;
`selectedIpContainsAddr` and `selectedIpContainsNet` reconstruct the one-field
records using only those actual extracted methods. The pinned Rust impls,
LLBC trait/method identities and generated wrapper projection are recorded in
[model-boundaries.md](model-boundaries.md). Astra reviewed this exact elaboration.

The previous 119 theorem identities and 36 public mappings are retained and
reaudited. Their constructor, observer, mask, boundary, truncation, conversion
and raw-constructor contracts are described in
[the arithmetic-core results](results-arithmetic-core.md).
The six new public mappings are **specializations of three generic methods**,
not six distinct inherent APIs: the ledger has 42 contract mappings for 39 API
forms under this convention. The six trait-body proofs and intermediate results
are helpers, not additional public coverage.

## Explicit semantic trust

The user-supplied [second expert response](expert-contains-review.txt) permits
small reviewed standard-library models after narrow extraction is investigated.
The [correspondence ledger](model-boundaries.md) distinguishes kernel-proved
connections from trusted Rust/model correspondence. An axiom-free Lean definition
does not prove its correspondence to Rust.

New reviewed boundaries in the version-local Aeneas `Std/NetIpAddr.lean` are:

- IPv4 and IPv6 concrete types with the same fixed-length octet fields as the
  previous generated types. Full input domains and independent values are unchanged;
  Rust representation/layout correspondence is now explicitly reviewed trusted.
- Only each concrete address type's `Ord::cmp`, modeled as normal success with
  comparison of existing U32/U128 big-endian byte interpretations. Correspondence
  to Rust's array/slice comparator is reviewed, not kernel-proved.
- For IPv6, this comparator boundary includes `segments()` and its native-endian
  transmute followed by `from_be`. No independent implementation proof of
  `segments()`, no generic transmute model, and no generic comparator model is claimed.

The actual `partial_cmp` bodies and ipnet Contains/public-wrapper bodies are
extracted and proved against the independent model. Default `le` is the existing
Aeneas `Std/Core/Cmp` model, connected to those extracted `partial_cmp` functions;
it is not a separately extracted Rust body. Its true cases are Some Less or
Some Equal, matching the reviewed pinned Rust default. Existing scalar and
big-endian byte models remain part of the baseline trust boundary.

`Proofs/Comparisons.lean` proves exact full Ordering, total Some partial comparison,
and numeric ≤ for this selected path. `OrderMath.lean` proves the bounded,
equal-length digit lexicographic/numeric correspondence; `Segments.lean` proves
mathematical byte pairing preserves value. Array-to-slice content preservation
is also checked. These helpers do not upgrade a reviewed Rust comparator boundary
into a proof of its Rust implementation.

Pinned extraction target: aarch64-apple-darwin, little endian, 64-bit pointers;
Rust commit 923c95cdf5ba65cea505aa2ea829f578e1506ed8. The verifier checks this
configuration and the reviewed Rust source hashes in
[std-source-boundaries.json](std-source-boundaries.json). These identity checks
are not semantic correspondence proofs. Rust-to-LLBC-to-Lean translation,
reviewed tool patches, selected library models and the Lean kernel remain trusted.

## Checks and evidence

- Unchanged upstream release 2.12.2 at
  13c5c5873c02127679b1e8e64b538e4e36942640; registry archive checksum
  791930b43c0d5973160d90a8f3894509f2b273430f5c5c73b668636d0287c5c0.
  The latest non-yanked stable release was resolved on 2026-10-16. Source inventory,
  Gitlink, tracked bytes and semantic Cargo build surface pass verification.
- Exact pinned tools, binaries, patches and actual Lake dependency checked;
  extraction Rust identity, target configuration and five reviewed core source
  hashes checked. Tool revisions remain in [toolchain.json](toolchain.json).
- Fresh shared extraction byte-identical to all maintained generated Lean.
  Only the two modeled concrete comparators are selected opaque; local application
  hiding and wildcard opaque selectors are rejected. Generated axioms and
  incomplete bodies remain forbidden. No generated Lean was hand-edited.
- Local Lake package cleaned and rebuilt; theorem kind, public mapping/precondition
  consistency and transitive dependencies audited: **158/158 passed**.
  Only propext, Classical.choice and Quot.sound are permitted. No sorryAx,
  application axiom or native-decision axiom was accepted.
- Eight kernel-checked shift-boundary examples passed.
- Native tests separately passed under default and no-default-features:
  **33 unit + 9 integration + 56 doc tests per setting**. The three new connection
  tests cover high-digit ordering, asymmetric IPv6 byte pairs, noncanonical
  containment, public dispatch and family separation. Finite tests add no formal
  coverage. Shared extraction/audit helper tests separately passed **12 tests**.
- All before/after input fingerprints match, including the new specifications,
  expert response, boundary ledger, source hashes, proof/model files and scripts.

The combined Aeneas patch retains checked shift wrappers and exact unused unwrap
Debug erasure, then adds concrete address model registrations and regenerated
metadata. The original Formatter model is unchanged. The Charon runtime-UB/panic
patch and proofs-rs audit-identifier patch remain enforced. Charon uses its pinned
Miri sysroot; optional diagnostic checks may be skipped, while scalar safety is
proved independently. This does not claim general const-evaluation, abort/unwind,
compiler equivalence or other-platform behavior. Details and rejected probes are
in [extraction-notes.md](extraction-notes.md).

## Remaining work and bugs

The next expert-recommended stateful target is `Ipv4AddrRange::next`, with one
contract specifying both the returned address and updated Nat half-open remaining
interval. All iterator transitions, hosts, subnet partition and aggregate union
preservation remain unproved. The four raw iterator constructor contracts prove
only exact storage. supernet/is_sibling, mask construction/parsing, other
conversions/traits, parsing/formatting, serde/schema contracts and optional
integrations remain outside accepted coverage. The empty extracted-but-unproved
list is not a whole-crate claim.

No new ipnet defect was observed in this continuation. The previously confirmed
schema output-conformance bug and permissive-schema mismatch remain recorded in
[bugs/README.md](bugs/README.md), with pinned standalone reproductions for a later
upstream PR. No issue, PR, login, push, upload or publication occurred.

## Reproduction and immutable run identity

Run `bash ipnet/2.12.2/scripts/verify.sh` from the repository root. Accepted and
rejected runs are preserved locally under ignored `verification/runs/` directories.
The preceding `check-nIBjBwK0` correctly rejected an in-flight metadata correction:
API labels were changed to their actual shared-reference type arguments. It has
no success result; the fresh accepted run above used fixed inputs throughout.

- Complete result SHA-256: 79306d4b2a92d45a128d76dcfc0818687632e8f08dcef4514d361ba2ba86c9f5
- Input fingerprint SHA-256: 60ddda8070dc0ab707d418c3863745234476915e5aefa1d56ca1a229ca4d264d
- Audit result SHA-256: 2888e20b6ba621e2076f8ea6f3740454489e07a11eed242671e50e3562d93f66

The result JSON records individual log/artifact hashes. This post-run summary is
outside the input fingerprint. Earlier results remain in results-initial-core.md
and results-arithmetic-core.md with their original evidence identities.
