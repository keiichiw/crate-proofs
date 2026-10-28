# Independent IPv6 iteration and remaining numeric contracts

Astra, 2026-10-16. Prospective specifications, not completed coverage claims.
Source: upstream/src/ipext.rs 150–262,395–422,564–648,699–736;
upstream/src/ipnet.rs IPv6 constructors and 1599–1704; upstream/src/mask.rs.
Baseline: check-UBTqNTpY, 403 audited theorems /112 API mappings.

## Representation and range constructor

Let W=2^128, M=W-1 and U=2^64-1. Address value is the independent
big-endian base-256 interpretation of all 16 stored octets. All raw endpoints
s,e in [0,M] are admitted. The remaining state is Empty when s>e, otherwise
Live(s,e+1), with Nat endpoints and cardinality L=e+1-s (Empty has L=0).
The exclusive endpoint W and cardinality W must not be squeezed into U128.
Ipv6AddrRange::new preserves both input addresses exactly and connects to this
remaining state. Empty concrete sentinels need not be identical.

## Nine overridden range iterator methods

Every mutating contract includes the actual normal result AND updated remaining
state simultaneously. None empties or preserves Empty as appropriate.

* next: Empty returns None; Live(s,t) returns s and remaining [s+1,t).
* next_back: Empty returns None; Live(s,t) returns t-1 and remaining [s,t-1).
* nth(n): for every Usize n on the pinned 64-bit target, if n<L return s+n
  and remaining [s+n+1,t); otherwise return None and Empty.
* nth_back(n): if n<L return t-1-n and remaining [s,t-1-n); otherwise None
  and Empty. Half-open intervals of zero length denote Empty.
* last and max return None iff Empty, otherwise Some(e), normally.
* min returns None iff Empty, otherwise Some(s), normally.
* size_hint normally returns (L,Some(L)) for L<=U, otherwise (U,None).
  It does NOT return a saturated upper bound. The entire IPv6 space is included.
* count normally returns exact L when L<=U. Under the pinned checked-overflow
  extraction it fails with integerOverflow when L>U. This is a full-domain
  classification, not a total-success claim or a saturating count. Native
  unchecked-overflow builds can wrap; that distinct profile is not covered.

Private count_u128 normally returns exact L when L<W; for the unique full
range s=0,e=M it fails integerOverflow in this checked model. Private
can_count_u128 normally returns exactly L<W. The public count full-range
failure can therefore arise before its usize overflow branch. nth/nth_back
and size_hint explicitly avoid that helper in the full-range case; all are
normally successful even there. State and no-revival laws should include
singleton 0, singleton M, reversed endpoints and full range, and any finite
sequence of the four mutating methods after exhaustion. Do not identify a
usize-limited count with mathematical cardinality W.

## IPv6 subnet constructor, raw next, and traces

Ipv6Subnets::new preserves start/end/minimum-prefix q exactly, for every U8 q.
A reversed state returns normal None without inspecting q and stays Empty.
For live s<=e and q<=128 define eligible heights
H={h | h<=128-q, s mod 2^h=0, 2^h<=e+1-s}. It contains 0. Let h=max H.
Actual next normally returns Some of the canonical network with stored value
s and prefix 128-h, preserving q and leaving remaining [s+2^h,e+1).
The selected block is the largest aligned eligible block starting at s;
its interval partitions the old interval with the residual, and positive
block size strictly decreases the Nat cardinality. Saturation at M must leave
an empty remaining state without revival. For live q>128, actual next fails
panic through new(...).unwrap(); this is the known raw invalid-prefix behavior,
not a newly discovered functional bug. No success-only restriction may conceal
this branch in the public mapping.

For q<=128, prove finite actual-call traces, each Some equation and final None
equation, exact interval union, canonical outputs, increasing order, pairwise
disjointness, nonempty blocks and greedy maximality. Trace length is at most
initial Nat cardinality. For a valid possibly noncanonical network (A,p),
p<=q<=128, its subnets(q) trace has exactly N=2^(q-p) outputs; output i<N is
(lower(128,A,p)+i*2^(128-q),q), and there are no later outputs. This is a
mathematical finite trace theorem, not a successful Vec allocation/collect claim.

## Remaining mask and arithmetic contracts

ipv6_mask_to_prefix(m) normally returns Ok(q) iff q<=128 and
value(m)=W-2^(128-q); Err PrefixLenError iff no such q exists. The q is unique.
Include zero,/128 and every noncontiguous mask. with_netmask(a,m) preserves the
exact original address/host bits and returns that q, or the same exact error.
checked_shl(128)=None and unwrap_or(0) is part of the all-ones path, not a
premise excluding it. Tagged mask dispatch must preserve each mask family's
width; mixed address/mask families are accepted iff the derived valid prefix
fits the address width, not rejected merely because tags differ.

The actual public IPv6 arithmetic overloads are: IpAdd<u128> -> Ipv6Addr with
value min(M,A+n); IpSub<u128> -> Ipv6Addr with value A-n (Nat subtraction);
IpSub<Ipv6Addr> -> u128 with value A-B. There is no IpAdd<Ipv6Addr> overload.
IpBitAnd/IpBitOr each have RHS Ipv6Addr and u128 and return Ipv6Addr whose value
is Nat bitwise AND/OR of the network-order operands. All inputs, no prefix
premises. Private IpStep helpers do not count as extra public APIs.

## Coverage inventory and external boundaries

Already covered network constructors/observers, numeric masks/network/broadcast/
trunc, contains, From<Ipv6Addr>, IpNet default/from, hosts/subnets initialization/supernet/sibling,
selected tags and structural derived traits remain separate accepted claims.
Ipv6Net::Default is still unmapped and must be selected/proved separately.
Prioritize the nine range methods, raw constructors, subnet next/traces, two
mask APIs and seven arithmetic/bitwise overloads above. Tagged IpAddrRange
iterator and IpSubnets next dispatch still need their actual forwarding-body
proofs. Aggregate, parsing, formatting, Hash, optional serde/schemars features,
and unselected iterator defaults/consumers are not implied by these results.
Parser has a recorded borrowed-callback blocker; aggregate needs sort and
mutable-iteration boundaries plus actual merge-loop proof. Markers Eq/Copy/
FusedIterator have no additional algorithm body.

Ipv6Addr::new is a possible narrow standard-library boundary, not permission
to model an ipnet application body. Its candidate executable semantics must
normally produce octets [a>>8,a mod256,b>>8,b mod256,...,h>>8,h mod256]
for all eight U16 segments. Review pinned Rust source and native-endian
transmute/to_be interaction before accepting; never apply endian conversion
twice. A kernel numeric bridge can establish value=sum(segment_i*2^(16*(7-i))),
but Rust memory-layout correspondence remains reviewed-trusted unless separately
proved. Prefer this concrete constructor boundary to a generic transmute model.
No new boundary is active solely because this prospective specification exists.

## Additional selected Ipv6Net default contract

Source ipnet.rs1364–1370: the actual Default::default body normally returns the
concrete Ipv6Net with all sixteen stored address octets zero and prefix U8 zero.
Equivalently its independent address value is 0 and prefix value is 0 (the
proved address-value injectivity determines the exact representation). It is
valid, canonical, and its represented set is all x with 0<=x<2^128. No input
premise is permitted. This is a separate concrete IPv6 default contract;
previous IpNet::default returns V4 zero/0 and does not establish this API.

## Full-family tagged iterator forwarding

Source ipext.rs424–474,650–666 and ipnet.rs1621–1629. These prospective contracts
cover BOTH V4 and V6 constructors, not merely V6 specialization. Interpret
remaining state as (family, independent half-open interval); family must not be
lost even for Empty. Every wrapper must refine its actual selected concrete
method, not a synthetic implementation of the mathematical operation.

For IpAddrRange next/next_back/nth/nth_back, all raw states and (for skips)
all Usize indices: normally return None or Some(IpAddr::Vf a) exactly matching
the concrete return, and IpAddrRange::Vf r' with the exact concrete updated raw
state. Compose this forwarding equality with the independent front/back/skip
interval contracts. No family switch, endpoint normalization or additional
prefix/endpoint-order premise. nth/nth_back use the pinned h64 premise; front
and back need no platform restriction. Empty state is preserved abstractly
but the concrete sentinel may change exactly as in the delegated operation.

last/max/min normally return the same-family tagged concrete endpoint or None,
with the existing all-raw endpoint semantics. size_hint under h64 returns the
independent (L,Some L) if L<=U, otherwise (U,None), for either family. V4 always
fits (L<=2^32); V6 includes L=2^128. count under h64 normally returns L for
V4 and for V6 L<=U; V6 L>U fails integerOverflow exactly. Preserve this failure
through the actual tagged dispatch. Do not advertise total count success for
the tagged type, and do not generalize checked64 behavior to release overflow
or a 32-bit target. These nine full-family methods are nine public bodies;
branch lemmas may be separate helpers, not duplicate API counts.

IpSubnets::next: for either tag Vf, the actual dispatch returns the exact
concrete next result, tagging Some network with IpNet::Vf and updated state
with IpSubnets::Vf. For width w=32 or128: reversed endpoints give normal None
and unchanged state for all q; live q<=w gives normal Some of the independent
greedy block and exact residual/unchanged q; live q>w fails panic. A failing
call has no promised returned state. Full-family dispatch must not assume q
valid globally, and family identity remains observable even in Empty states.
Finite actual traces can be obtained by lifting concrete call equations with
exact tags; such a corollary is separate from the one-step public mapping.
