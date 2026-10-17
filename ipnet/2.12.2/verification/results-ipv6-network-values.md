# Local verification results — ipnet 2.12.2

Accepted run: **2026-10-16**, [check-UBTqNTpY](runs/check-UBTqNTpY/result.json).
The full verifier passed with **403 audited theorems: 112 public contracts and
291 helpers**. All previous 369 theorem identities are retained. This adds
20 public contracts and 14 helpers; contract counts include family specializations
and are not counts of distinct Rust method names. Astra independently specified
and reviewed both ordered stages; Sol proved actual extracted bodies. The primary
reviewed statements, mappings, trust scope and reproducible evidence.

## First stage: IPv6 network methods and tagged dispatch

Four concrete Ipv6Net contracts and the four corresponding IpNet V6 cases:

- hosts: exact full-block start/end and independent remaining interval. Both
  endpoints are included at every prefix; /0 represents all 2^128 addresses,
  /127 two and /128 one. The cardinality is a Nat, with no machine-integer
  representability assumption.
- subnets: for every U8 requested prefix q, ordinary Err exactly when q is less
  than the stored prefix or greater than 128; otherwise exact initial endpoints
  and minimum prefix. Tagged success preserves the V6 variant.
- supernet: None for /0, otherwise the canonical immediate parent at prefix p-1,
  with the original block contained in it. The actual wrapping-subtraction
  implementation's /0 path is included.
- is_sibling: true exactly for positive equal prefixes and equal immediate parent
  blocks, including self-comparison and different stored host bits in one child.

These network contracts require valid stored prefixes ≤128 and permit arbitrary
host bits. They prove range/subnet initialization and network relations, **not
IPv6 iterator next, enumeration, count or allocated collection success**.

The four previously extracted-but-unproved V6 dispatch cases are now discharged.
Together with the earlier V4 and mixed sibling contracts, the selected dispatch
bodies have the stated valid-input behavior on all family branches.

## Second stage: IPv6 structural value traits

Actual clone, eq, cmp and partial_cmp are proved for each of Ipv6Net,
Ipv6AddrRange and Ipv6Subnets (12 contracts). They apply to every raw state,
including prefixes above 128, reversed endpoints and noncanonical host bits.
Clone returns the exact original value. Equality and lexicographic ordering use
stored fields in declaration order with independent big-endian numeric addresses;
partial_cmp returns Some of the full Ordering. This is structural equality,
not equality of represented CIDR sets. Copy/Eq markers, Hash and inherited defaults
are not extra verified algorithms.

The 14 helpers establish width-128 host/parent arithmetic and actual address
equality connected to 16-octet numeric injectivity. See
[independent specification](ipv6-tagged-value-specification.md),
[IPv6 coverage](ipv6-coverage.md), and proof modules IPv6NetMath, IPv6NetOps,
TaggedIPv6, IPv6AddressEq and IPv6Derived.

## Preserved scope, trust and remaining work

The [previous report](results-tagged-ipv4.md) records the retained IPv4/tagged
contracts and links the earlier complete IPv4 subnet trace proofs. Existing
64-bit restrictions on Usize-sensitive range methods remain unchanged.
There are zero selected-but-unproved inventory entries; this is selected-scope
completion, **not whole-crate verification**.

No ipnet source, tool implementation or semantic model was changed. Existing
scalar, address/comparison and Array/Slice models remain trusted correspondences.
The reviewed drop-free Result::ok boundary now explicitly includes
Result<Ipv6Net,PrefixLenError>, using the unchanged match/discard model. The IPv6
comparator remains a reviewed trusted correspondence, not a proved Rust comparator
implementation. See the [model ledger](model-boundaries.md). Kernel axiom audits
do not prove Rust-to-LLBC-to-Lean translation or source/model correspondence.

Remaining work includes IPv6 address/subnet iteration, aggregate, textual parsing
and formatting, tagged next/mask dispatch, Hash, inherited consumers, allocation,
and optional serde/schema integrations. Known extraction/backend limitations
remain in [extraction notes](extraction-notes.md) and the
[parser blocker record](blockers/ipv4-parser-callback/README.md).
No new ipnet bug was found. Existing [bug records](bugs/README.md) are preserved
for later upstream PRs. No push, issue, PR or publication occurred.

## Reproducible evidence

- Pinned unchanged source/release/Gitlink/build surface and exact tool source,
  binary and compatibility-patch checks passed.
- Fresh extraction byte-matched every maintained generated model.
- Clean Lake build, all 403 theorem/mapping/transitive axiom checks and eight
  kernel shift checks passed. Only propext, Classical.choice and Quot.sound
  are allowed; no sorry, custom or native-decision axioms.
- Native default and no-default-features each passed 33 unit + 17 integration
  + 56 doc tests (106 each), separately from formal proof.
- Before/after input fingerprints match. The primary independently rechecked
  all saved artifact hashes, the current fingerprint and retention of all
  previous 369 theorem identities.

Run `bash ipnet/2.12.2/scripts/verify.sh` from repository root. Evidence is local
in the ignored run directory. This report is excluded from fingerprints.

- Complete result SHA-256: 5273141e16fffabc3e7b6d9b9909932993a1f4dc7d661910e14d3b7219ff3214
- Input fingerprint SHA-256: 11001e550fedb1d8fb16aa9e4c20e79142191a0875b9cc3aa9ff4e8a4447b2ae
- Audit result SHA-256: 85db9a272f1eb61580b8c447e85ca2f2130c93f436f2dd82e72a1108fec29cdc
