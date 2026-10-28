# Independent IPv4 tagged dispatch and value contracts

Astra specification, 2026-10-16, preserving all accepted contracts. This batch
excludes the known parser translation blocker; it does not infer verification
of an entire tagged API from one family specialization. Source bodies inspected
in ipnet.rs, ipext.rs and mask.rs. Actual extracted methods must be selected;
synthetic replacements for derived methods do not constitute implementation proof.

## Priorities and exact tags

First select the two From conversions and concrete V4 tagged forwarding bodies;
then derived value methods if their actual generated bodies extract. These need
no new CIDR algorithm models. Aggregate remains a separate substantial goal.

For every raw Ipv4AddrRange r, From into IpAddrRange normally returns exactly
V4(r), preserving both endpoint addresses. For every raw Ipv4Subnets r, From
into IpSubnets normally returns exactly V4(r), preserving both addresses and
all U8 q, including q>32. Do not add range-order or validity premises.

For IpSubnets::next on V4(r), preserve the complete frozen concrete raw-domain
classification. If concrete next normally returns (o,r'), the tagged call
normally returns (o.map IpNet::V4, IpSubnets::V4(r')). Combine this actual-call
bridge with independent bestPrefix/residual/q-preservation observations. Empty
ranges return None for every q; live q≤32 gives the canonical greatest fitting
block; live q>32 takes the same modeled panic. No tag can silently change.
A forwarding identity alone is a useful helper; completed public coverage must
connect it to the independent behavior. Finite traces/fixed-q sequences can then
be tagged pointwise, without assuming runtime list collection succeeds.

## IpNet methods on a V4 receiver

For a valid possibly noncanonical stored IPv4 network n=(a,p), p≤32, define
lo=floor(value(a)/2^(32-p))*2^(32-p), hi=lo+2^(32-p)-1.

* hosts normally returns IpAddrRange::V4 with exact endpoints lo+1,hi-1 if
  p<31, otherwise lo,hi; use the accepted remaining-interval interpretation.
* subnets(q), for every U8 q, normally returns ordinary Err PrefixLenError
  exactly when q<p or q>32. Otherwise it returns Ok(IpSubnets::V4(r)) with
  exact start lo/end hi/minimum q. Constructor and enumeration remain distinct.
* supernet normally returns None for p=0. Otherwise it returns Some(IpNet::V4
  parent) with prefix p-1 and canonical address lower(32,value(a),p-1), whose
  set contains n. Preserve the full noncanonical input domain.
* is_sibling(V4 n,V4 m), with both valid, is true exactly when p>0, the two
  prefixes agree, and their canonical immediate-parent lower values agree.
  Self and two raw addresses representing one child are included. Mixed tags
  return false in either direction. Since the mixed-tag implementation does
  not inspect either prefix, no prefix-validity premise is needed for that case.

Each contract is total normal success in its specified domain, including
ordinary errors. Label V4-only specialization as such in the API mapping.

## Mask dispatch and mixed-family caution

The public ip_mask_to_prefix(V4 m) returns normal Ok(q) exactly for every U8 q
satisfying q≤32 and value(m)=2^32-2^(32-q), otherwise normal Err. This is a
V4 dispatch specialization of the public function, not its V6 proof.

IpNet::with_netmask(V4 ip,V4 mask) returns normal Ok(V4 {addr=ip,prefix=q})
exactly for the same IPv4 contiguous-mask relation; otherwise normal Err.
The stored input ip and host bits are preserved exactly.

A V4 address with a V6 mask is NOT rejected merely for differing families.
If a full V4-address/all-mask contract is selected, define width w from the mask
family, and accept exactly when some q≤w has mask value 2^w-2^(w-q) AND q≤32.
The result still has V4 tag and the original ip. Thus V6 /0 through /32 masks
can succeed; V6 prefixes above32 and every noncontiguous mask fail. A V4/V4-only
contract is an honest staged specialization but must not be labeled full V4
receiver coverage. Conversely V6 address with contiguous V4 mask can accept all
its prefixes; that is outside this batch unless explicitly selected.

## Derived value traits

For Ipv4Net use the independent structural key (ipv4Value(stored addr),prefix).
Equality is key equality, NOT equality of represented CIDR sets. Comparison
is full lexicographic Nat ordering by stored address first, then prefix, with
all three Ordering outcomes. Partial comparison returns normal Some of that
same ordering. Boolean comparison methods, if separately selected, return their
exact corresponding order predicates. Clone returns the exact original struct.
These contracts apply to all raw addresses and all U8 prefixes, including >32:
these value operations do not invoke CIDR arithmetic or construction. If actual
publicly constructible states are used instead, do not weaken a naturally raw
contract merely to simplify proofs.

For Ipv4AddrRange, the analogous key is (start value,end value). For Ipv4Subnets,
it is (start value,end value,q), matching declaration field order. All raw
endpoints and q are included; Clone preserves all fields. Derived Ord's default
min/max/clamp and Clone::clone_from require their own actual-body connections if
claimed, rather than being counted implicitly. Eq and Copy are marker traits
without algorithm bodies; do not add separate API counts for marker declarations.
Hash requires a hasher-effect contract and is not established by equality proofs.

## Full-tag default and address conversions

Source `ipnet.rs:565–568` defines Default for IpNet as V4 of IPv4 default.
Require ordinary normal success with exact V4 tag, zero stored IPv4 address and
prefix zero. This is the IPv4 all-address network, not a singleton.

For every IpAddr input, From<IpAddr> for IpNet normally returns the same family
and exact stored address: V4(a) becomes V4({addr=a,prefix=32}), and V6(a)
becomes V6({addr=a,prefix=128}). No input precondition is needed. The represented
set is therefore the singleton of that tagged address; do not confuse these
From results with Default. Source lines 598–604 dispatch to concrete conversions.

The co-selected public From<Ipv6Addr> for Ipv6Net has its own exact normal-result
contract {addr=a,prefix=128} for every address (source lines 1385–1388). It may
be separately mapped only when its actual extracted body is proved, as it is
a distinct public implementation rather than a second name for the generic
conversion theorem. Existing From<Ipv4Addr> coverage remains unchanged.

The analogous raw IPv6 iterator conversions, when co-selected, normally return
exactly IpAddrRange::V6(r) and IpSubnets::V6(r) respectively for every raw input.
All endpoint fields and every U8 minimum prefix are preserved. These are storage
and tag contracts only; they do not assert IPv6 iteration correctness.
