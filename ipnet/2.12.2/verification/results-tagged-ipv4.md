# Local verification results — ipnet 2.12.2

Accepted run: **2026-10-16**, [check-RgsjCQby](runs/check-RgsjCQby/result.json).
The complete verifier passed with **369 audited theorems: 92 public contracts
and 277 helpers**. All previous 344 theorem identities are retained. This
continuation adds 25 public contracts, including explicit family specializations;
these counts are not counts of distinct Rust method names or whole-crate coverage.
Astra independently specified/reviewed all 25 additions; Sol proved actual
extracted bodies. The primary reviewed scope, mappings and reproducible evidence.

## Added contracts

- Actual Clone::clone, PartialEq::eq, Ord::cmp and PartialOrd::partial_cmp for
  Ipv4Net, Ipv4AddrRange and Ipv4Subnets (12 contracts). Independent keys use
  stored address/prefix or endpoints/prefix, in declaration order. Every raw
  state is included, including invalid prefixes and reversed endpoints.
  Structural equality is distinct from equality of represented CIDR sets.
- Raw-preserving From conversions from both IPv4/IPv6 address ranges and subnet
  iterators into their tagged enums (4 contracts).
- IpNet::hosts, subnets, supernet and is_sibling on V4 inputs (4 contracts).
  Valid IPv4 network prefixes are required, while noncanonical host bits are
  permitted. subnets covers all requested U8 prefixes including ordinary Err.
  hosts retains /31 and /32 behavior; supernet returns the canonical parent
  or None for /0; siblings use equal positive prefix and equal parent block.
- Mixed V4/V6 and V6/V4 sibling calls return false, without validity premises
  (2 contracts).
- Full IpNet Default is V4 zero/0; full From<IpAddr> preserves family and original
  address with prefix 32 or 128; From<Ipv6Addr> for Ipv6Net preserves the address
  with prefix 128 (3 contracts).

The implementation proofs are in IPv4Derived, IPv4IteratorDerived, TaggedIPv4
and TaggedDefaultFrom. See the [independent specification](ipv4-tagged-value-specification.md).

## Preserved scope and remaining work

The [previous accepted report](results-subnets-parser-blocker.md) records the
complete IPv4 subnet raw-state classification and actual finite/fixed-prefix
traces. These remain checked, including greedy maximal blocks, exact residuals,
termination, ascending disjoint exact union and constructor-origin counts.
Logical traces do not assert successful allocated Vec collection. Earlier
64-bit restrictions on Usize-sensitive range methods remain unchanged.

Four selected generic-body cases are explicitly **extracted but unproved**:
IpNet::hosts(V6), subnets(V6), supernet(V6), is_sibling(V6,V6). The V4 contracts
do not establish those V6 cases. Simple V6 constructor proofs do not establish
V6 iterator behavior.

Other remaining work includes aggregate, textual parsing/formatting, Hash,
inherited trait defaults and iterator consumers, allocation, optional serde/schema
integrations and other-family iteration. Tagged range/subnet next reaches an
unsupported IPv6 constructor transmute; mask dispatch and tagged with_netmask
hit a generated Lean parameter/namespace shadowing error; Hash leaves unmodeled
hasher effects. These paths were excluded from this no-tool-patch continuation.
See [extraction notes](extraction-notes.md) and the
[remaining coverage inventory](ipv4-remaining-coverage.md).
The known [parser borrowed-callback blocker](blockers/ipv4-parser-callback/README.md)
was bypassed by selecting other APIs, not resolved or modeled away.

No new semantic model, tool patch or upstream source change was introduced.
Existing scalar, concrete-address/comparison, memory/Array/Slice and trailing-zero
models, together with Rust-to-LLBC-to-Lean translation, remain trust boundaries.
A kernel axiom audit does not prove Rust/model correspondence. See the
[model ledger](model-boundaries.md).

No new ipnet bug was found during this continuation. Existing
[bug records](bugs/README.md), including the heapless feature defect, remain
available for later upstream PRs. No issue, PR, push or publication occurred.

## Reproducible evidence

- Pinned unchanged source/release/Gitlink/build-surface and exact tool source,
  binary and compatibility-patch checks passed.
- Fresh extraction byte-matched the maintained generated model.
- Clean Lake rebuild, all 369 theorem/mapping/transitive axiom checks and eight
  kernel shift checks passed. Only propext, Classical.choice and Quot.sound
  are allowed; no sorry, custom or native-decision axioms.
- Native default and no-default-features each passed 33 unit + 17 integration
  + 56 doc tests, separately from formal proof.
- Before/after input fingerprints match. The primary independently rechecked
  every recorded artifact hash, current input fingerprint and retention of all
  previous 344 theorem identities.

Run `bash ipnet/2.12.2/scripts/verify.sh` from repository root. Evidence stays
local in the ignored run directory. This report is excluded from fingerprints.

- Complete result SHA-256: c7d32a91d19d080cf6523afd20bd4448482236f6ae7328ed8e628ec0eab12ba1
- Input fingerprint SHA-256: 77a8813135d806511d44d8eb3a738f572f83ed169e2256e32a1ecff79a99c9c4
- Audit result SHA-256: 8848ade1c4c823c326bc3f3d7655fb4be200aa0ba3ffb05a9eb74e77cbaeb0df
