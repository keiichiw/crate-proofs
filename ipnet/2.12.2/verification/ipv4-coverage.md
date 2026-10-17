# IPv4 coverage ledger

This file separates actual contracts from derived helpers and generic/optional
APIs. The accepted run in results.md and theorem inventory determine completed
coverage. Specifications and extracted bodies alone do not establish it.

## Accepted before the current expansion

- Ipv4Net: new, valid-prefix new_assert, addr, prefix_len, max_prefix_len,
  netmask, hostmask, network, broadcast, trunc, built-in contains address/network.
- Ipv4AddrRange: raw new and stateful next.
- Ipv4Subnets: raw new storage; subsequent iteration results are listed below.
- Other accepted IpNet/Ipv6Net contracts remain in the full inventory; a proof
  about Ipv4Net does not establish unselected enum dispatch or IPv6 bodies.

## Additional contracts (acceptance evidence in results.md)

- Ipv4AddrRange: next_back, nth, nth_back, count, size_hint, last, min, max.
  Every raw endpoint pair is included. Usize-sensitive contracts state their
  platform condition explicitly; full-range length 2^32 is included at 64 bits.
- Ipv4Net: hosts, supernet, is_sibling, subnets initialization, Default and
  From<Ipv4Addr>. Valid prefix is the only CIDR assumption; arbitrary host bits
  remain permitted. Constructor errors are preserved; actual enumeration is now
  connected by the audited subnet trace theorems.
- Ipv4Addr public IpAdd<u32> and IpSub<u32>/IpSub<Ipv4Addr> saturating operations.
  Internal IpStep functions and scalar-model helpers are not public API entries.
- ipv4_mask_to_prefix and Ipv4Net::with_netmask: all-input exact success/error iff
  for contiguous masks, preserving the original address on construction.
- IpBitAnd and IpBitOr on IPv4 addresses with either address or u32 RHS: exact
  independent network-order numeric bitwise result for all inputs.

- Ipv4Subnets::next: full raw-state classification (empty normal None for all q,
  nonempty q≤32 maximal CIDR and residual, nonempty q>32 modeled panic).
- Actual finite subnet call traces: termination, canonical ascending disjoint
  exact union, plus constructor-origin fixed-q indexed outputs and count.
  Accepted in check-rgPh4e3G (340 theorems/67 public contracts); logical traces
  do not imply allocated Vec collection success.

## Remaining IPv4 work

- Ipv4Net::aggregate exact union/minimality.
- Parsing/FromStr, Display/Debug formatting, and parsing/formatting roundtrips.
- Hash, Debug, inherited comparison/clone defaults and conversions not individually mapped;
  generic inherited Iterator consumers/combinators, collection allocation.
- serde and optional JSON-schema integrations, serialization roundtrips and
  schema soundness/completeness; native schema bug reproductions are not proofs.
- Panic behavior outside valid-prefix new_assert, cross-platform overflow/usize
  behavior, and const-evaluation are outside the selected runtime guarantees.

No implicit whole-type or whole-crate coverage follows from these lists.

## Value traits and tagged IPv4 expansion

Subject to the acceptance evidence in results.md, the maintained expansion adds
actual clone/eq/cmp/partial_cmp for Ipv4Net, Ipv4AddrRange and Ipv4Subnets.
The specification uses stored field keys, including noncanonical host bits,
reversed endpoint ranges and every raw U8 prefix. Structural comparison does
not equate different stored representations of the same CIDR set. Copy/Eq
markers and inherited defaults do not acquire extra API coverage.

Raw IPv4 range/subnet conversions preserve the full value in the V4 tag.
IpNet hosts/subnets/supernet/is_sibling are covered only on the stated V4
inputs; mixed sibling tags return false without validity premises. V6-only
paths are not established by these contracts; the separate IPv6 continuation
is tracked in ipv6-coverage.md. Tagged iterator next, mask dispatch and tagged
with_netmask remain unverified. A selected generic body is not an all-variant
coverage claim.

The additional full-family From<IpAddr> contract preserves the stored family
and address and sets prefix 32 or 128; IpNet Default is exactly V4 zero/0.
The co-selected IPv6 address-to-network and raw range/subnet tag constructors
also have exact preservation contracts. These simple V6 conversions do not
establish V6 iterator behavior.
