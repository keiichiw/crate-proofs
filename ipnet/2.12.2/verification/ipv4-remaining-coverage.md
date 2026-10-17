# Remaining IPv4 coverage inventory

Independent source inventory, 2026-10-16. Baseline accepted evidence is
`check-YVXW5GtO` (344 audited theorems / 67 mapped contracts across all families).
This is an inventory, not an extension of accepted verification claims.

## Concrete default-feature IPv4 surface

`Ipv4Net` has 17 inherent method names: new, new_assert, with_netmask, trunc,
addr, prefix_len, max_prefix_len, netmask, hostmask, network, broadcast, supernet,
is_sibling, hosts, subnets, contains, aggregate. All except aggregate have
accepted mappings; contains is specialized separately for address and network.
new_assert's accepted contract is for valid prefixes; invalid-prefix panic is
not thereby covered. subnets now also has an audited actual fixed-prefix enumeration trace.

| Surface | Accepted versus remaining |
| --- | --- |
| Ipv4Net::aggregate | Remaining substantive whole-list API; sorting, merging, actual mutable update and subnet extension must compose. |
| FromStr for Ipv4Net | Remaining; complete ASCII grammar/ordinary error iff, host-bit preservation and no parser panic. |
| Display and Debug for Ipv4Net | Remaining; default text is original address/prefix, Debug delegates Display. Sink failure propagation and formatter behavior are separate from a successful String roundtrip. |
| Default and From<Ipv4Addr> for Ipv4Net | Accepted exact value contracts. |
| Contains bodies | Accepted through concrete and public specialization theorems; trait is in a private module and used through public inherent dispatch. |
| Derived value traits for Ipv4Net | Current expansion proves actual Clone::clone, PartialEq::eq, Ord::cmp and PartialOrd::partial_cmp for every raw prefix, against structural address+prefix keys. Acceptance is determined by results.md. Copy/Eq markers add no executable contract. Hash, Debug, and inherited comparison/clone defaults remain separate. |
| Ipv4AddrRange::new and nine overridden iterator methods | Accepted new, next, nth, count, size_hint, last, min, max, next_back, nth_back. |
| Ipv4Subnets::new | Accepted exact raw storage; next raw-state classification and compositional actual enumeration are now checked. |
| Ipv4Subnets FusedIterator | Marker has no executable body; actual empty-next no-revival law is proved, not a separate API body count. |
| Ipv4AddrRange FusedIterator | Actual next no-revival laws exist; marker implementation itself is not an extra algorithm. |
| Derived value traits on Ipv4AddrRange/Ipv4Subnets | Current expansion targets actual clone/eq/cmp/partial_cmp against stored endpoint/prefix keys, with all raw states. Acceptance is determined by results.md. Debug, Hash and inherited defaults remain; markers add no algorithms. |
| IpAdd<u32>, IpSub<u32>, IpSub<Ipv4Addr> for Ipv4Addr | Accepted three exact full-domain arithmetic contracts. |
| IpBitAnd / IpBitOr for Ipv4Addr with address/u32 RHS | Accepted four exact full-domain bitwise contracts. |
| ipv4_mask_to_prefix | Publicly re-exported free function, accepted complete mask iff. |

`IpStep` is internal (not re-exported), despite its `pub` declaration in the
private ipext module. Its helpers are not additional public API coverage.
`Parser` is likewise inaccessible through the public crate API.

## Tagged IPv4 paths

Do not conflate concrete IPv4 completion with every V4 path of a tagged API.
From<Ipv4Net> for IpNet is mapped. The current expansion adds raw-preserving
From<Ipv4AddrRange> for IpAddrRange and From<Ipv4Subnets> for IpSubnets,
and V4-specialized IpNet::hosts/subnets/supernet/is_sibling contracts.
Mixed V4/V6 sibling calls are false with no validity premise. See results.md
for acceptance evidence; generic V6 hosts/subnets/supernet and V6/V6 sibling
are not established by the V4 specializations. Their subsequent separate IPv6
proofs are tracked in ipv6-coverage.md and the accepted result report.

Full IpNet Default and From<IpAddr>, and both-family raw range/subnet tag
conversions, are also included in this expansion. Tagged range iterator
dispatch, IpSubnets::next, IpNet::aggregate/with_netmask, FromStr and
formatting remain separate obligations.
IpNet basic constructors/observers/arithmetic and contains already have mappings.
The public free ip_mask_to_prefix dispatch also needs its own mapping.
Mixed-family with_netmask behavior must retain the actual prefix-width rule,
rather than inventing a same-family requirement.

The no-tool-patch probes defer tagged range/subnet next because the dependency
closure reaches unsupported IPv6Addr::new transmute. ip_mask_to_prefix and its
with_netmask caller fail generated Lean compilation: the argument named `mask`
shadows the `mask` namespace in branch calls. Hash leaves unmodeled U8/U32 hasher
effects. These paths are excluded rather than replacing their bodies or adding
axioms. Parser's separate borrowed-FnOnce-state blocker remains documented in
blockers/ipv4-parser-callback/README.md.

## Inherited consumers and optional features

Standard Iterator defaults and adapters (for example fold, try_fold, collect,
map, filter, take, skip, enumerate, position, all, any, sum and product), and
DoubleEndedIterator defaults such as rfold/try_rfold/rfind, are not all proved
by proving next. Their concrete application requires an implementation or
reviewed library correspondence plus callback/termination/length relations.
Blanket trait methods and auto traits are not independently implemented ipnet
algorithms. No claim of universal consumer verification is justified.

Optional serde Serialize/Deserialize for Ipv4Net and the V4 IpNet variant remain
unproved, including human-readable text and non-human-readable five-octet tuple
forms. heapless and legacy ser_as_str alter the intended text serialization
path. JsonSchema implementations for schemars08/schemars1 and legacy aliases
are outside default-feature formal scope; previously recorded schema defects
remain separate. no_std compilation/behavior is also not implied by the pinned
default-feature extraction. Shared PrefixLenError and AddrParseError formatting,
Error and derived traits are support API surfaces rather than CIDR algorithms.

## Parser/format source review

Ipv4Net Display writes original stored address, '/', and decimal prefix; it
intentionally preserves host bits. Debug delegates to it. The parser accepts
four 1..3-digit ASCII decimal octets (≤255), slash and a 1..2-digit decimal
prefix (≤32), with full EOF. Leading zeros are accepted; whitespace/signs and
non-ASCII digits are not. Default valid network formatting therefore lies in
the parser's grammar. The numeric parser rejects once digit count exceeds its
small bound, so long input does not by itself imply U32 arithmetic overflow.
No concrete default-feature IPv4 parser/format counterexample was established
by this source inspection; this is not a formal parser proof.

New candidate found during optional-feature review: the documented `heapless`
feature enables dependency heapless and serde, but the stack-buffer serializer
branches in ipnet_serde.rs are guarded only by legacy `ser_as_str`. Thus enabling
heapless alone still selects collect_str. This cfg mismatch is now confirmed by the isolated native reproduction
`bugs/heapless-feature-repro` (IPNET-003): identical output with 3 allocation/
reallocation calls for heapless-only and zero for the legacy feature. It is
distinct from previously known schema defects and raw invalid-prefix panic.
