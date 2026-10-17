# Independent IPv6 network, tagged and derived-value contracts

Astra specification, 2026-10-16. Baseline accepted run check-RgsjCQby has
369 audited theorems / 92 mappings. The contracts here extend the selected scope;
they are not claims of completed verification. Source reviewed: ipnet.rs
1195–1288, the IpNet dispatch bodies, and declaration field order of Ipv6Net,
Ipv6AddrRange and Ipv6Subnets. Parser and aggregate remain separate work.

## Independent address/set meaning and domain

Interpret the 16 stored octets as their big-endian base-256 Nat value A, with
0≤A<2^128. For a valid network prefix p≤128, put K=2^(128-p),
lo=(A/K)*K, hi=lo+K-1. Its set is the inclusive interval [lo,hi]. All input
host bits are permitted. Use arbitrary-precision Nat endpoints and lengths;
hi+1 may equal 2^128. No U128/usize representability assumption on this exclusive
endpoint or interval length is permitted. No host alignment premise is needed.

## Concrete Ipv6Net prerequisites

Each theorem targets the actual extracted method and includes ordinary normal
success, including ordinary errors. For all valid possibly noncanonical n:

* hosts returns an Ipv6AddrRange with exact numeric start lo and end hi, and
  abstract remaining interval [lo,hi+1). No endpoints are excluded at ANY
  prefix. /0 includes every address, /127 includes two, /128 one. This proves
  initialization, not IPv6 iterator enumeration or count/collection success.
* subnets(q) for every U8 q returns ordinary Err PrefixLenError exactly when
  q<p or q>128; otherwise Ok of exact raw state start lo, end hi, minimum q.
  No other ordinary error is permitted. This proves construction only; no
  IPv6 subnet-next or finite enumeration guarantee is implicit.
* supernet returns None exactly for p=0. For p>0 it returns Some parent with
  exact prefix p-1 and canonical stored numeric address lower(128,A,p-1).
  Parent is valid and contains the whole original network set. The source's
  wrapping subtraction at /0 must lead to ordinary None, not be excluded.
* is_sibling(n,m), for both valid, returns true exactly when p>0, p=m.prefix,
  and lower(128,A,p-1)=lower(128,value(m.addr),m.prefix-1). Self and different
  stored addresses representing one child are included; do not add distinctness
  or disjointness. It is immediate-parent equality, not arbitrary shared ancestry.

## IpNet V6 dispatch

Select actual IpNet bodies on V6 receivers and connect to the preceding
independent contracts. hosts returns exactly IpAddrRange::V6 of the specified
state. subnets returns exact errors or Ok(IpSubnets::V6 specified state).
supernet returns None or Some(IpNet::V6 canonical parent), with exact prefix
and containment. is_sibling(V6 n,V6 m) has the same-parent iff above. Previously
checked mixed-family false laws remain unchanged and require no validity
premise because that branch does not inspect fields. Label selected mappings
as V6 specializations; no V4 proof is replaced, and an unselected mask/parser
or iterator method is not covered by these forwarding theorems.

## Twelve actual derived-value contracts

For each of Ipv6Net, Ipv6AddrRange and Ipv6Subnets, independently specify the
structural key in declaration order:

| Type | Key |
| --- | --- |
| Ipv6Net | (value(stored addr), prefix.val) |
| Ipv6AddrRange | (value(start), value(end)) |
| Ipv6Subnets | (value(start), value(end), min_prefix.val) |

For ALL raw fields, Clone normally returns the exact original structure;
PartialEq::eq normally returns a Boolean iff these keys are equal; Ord::cmp
normally returns the full lexicographic Ordering of these Nat keys; and
PartialOrd::partial_cmp normally returns Some of the same Ordering. This
includes every U8 prefix through255, reversed endpoints and arbitrary host
bits. Value traits do not invoke CIDR arithmetic and must not inherit its
valid-prefix condition. Two different empty raw states can compare unequal;
set equality or remaining-interval equality is not the structural contract.
Only actual generated derived bodies qualify. Eq/Copy markers are not extra
algorithms, and Hash/default comparison consumers are not silently included.

## Reuse, trust, and useful derived laws

Reuse the accepted independent ipv6Value, address conversions, full Ordering
comparison and network/broadcast/trunc Nat contracts. Address comparison retains
the reviewed concrete IPv6 comparator boundary, including its previously
recorded segment/byte-layout correspondence. Do not reclassify it as a proved
Rust sort/comparator implementation. For structural address equality, prefer
actual extracted equality through existing Array/Slice scalar equality models
and the width-independent base-256 list injectivity proof; specialize to length
16 rather than introducing a new equality model.

Supernet's concrete Result::ok use is Result<Ipv6Net,PrefixLenError>, both
drop-free. Extend the existing narrowly reviewed drop-free boundary explicitly
if it is selected; generic destructor effects remain unproved. Result::map
should retain actual extraction as in the IPv4 path.

Useful subsequent laws may prove clone identity, equality reflexivity/symmetry/
transitivity, comparison consistency with key equality and lex ordering,
mutual cmp reversal, or supernet/sibling invariance under trunc on either side.
They must cite the actual method equations, preserve the domains above, and be
classified as derived laws/helpers rather than additional public API bodies.
No native finite test alone establishes any of these contracts.
