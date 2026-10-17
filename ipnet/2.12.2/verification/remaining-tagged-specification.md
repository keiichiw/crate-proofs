# Independent remaining tagged-value and constructor contracts

Astra, 2026-10-16. Baseline check-dxnxYoEp: 588 audited theorems /142 API
mappings. These are prospective contracts; no extraction-only success implies
proof. Source reviewed: upstream/src/ipnet.rs enum declarations, new_assert,
with_netmask; upstream/src/ipext.rs tagged range declaration; mask.rs dispatch.

## Twelve tagged derived-value bodies

For each of IpNet, IpAddrRange, IpSubnets, assign family rank 0 to V4 and 1 to
V6. Interpret each stored address by independent network-order byte value.
The structural keys are:

* IpNet: (family rank, stored address value, stored prefix value).
* IpAddrRange: (family rank, stored start value, stored end value).
* IpSubnets: (family rank, stored start value, stored end value, stored q).

For ALL raw payloads (every U8, noncanonical host bits, reversed endpoints),
actual Clone::clone normally returns the exact tagged input; PartialEq::eq
normally returns a Boolean iff keys are equal; Ord::cmp normally returns the
full lexicographic Ordering of these Nat keys; PartialOrd::partial_cmp normally
returns Some of that same Ordering. In particular V4 < V6 regardless of numeric
payload, mixed tags are never equal, and empty states retain their structural
identity. Same-family keys compare address then subsequent fields in declared
order. No valid-prefix or nonempty-state premise is permitted. This is stored
value semantics, not CIDR-set or remaining-set equality. Prove selected actual
derived bodies, using prior concrete body contracts; no synthetic application
comparator registration. Twelve methods, one mapping per full-family method;
branch and math lemmas are helpers. Copy/Eq markers add no algorithm coverage.

## Runtime new_assert invalid-prefix completion

Ipv4Net::new_assert(a,p), for every U8 p>32, panics in Rust; its extracted `massert` fails `.assertionFailure`. Ipv6Net::new_assert(a,p), for p>128, likewise fails `.assertionFailure`. IpNet::new_assert
on either address tag fails `.assertionFailure` iff its p exceeds that address family's width;
otherwise it normally returns that same tag and exact original stored address
and prefix. The concrete full-domain contracts have the same valid/invalid split.
No host-bit restriction. Valid branches retain previously accepted contracts.
Invalid branch proofs strengthen coverage of these existing public APIs, not
new API identities; report helper counts separately. Runtime failure does not
establish const-evaluation diagnostics, panic-message text, unwind/abort behavior,
or any post-panic returned value/state. The modeled error is `.assertionFailure`, not `.panic` or PrefixLenError.
This exact error classification follows existing Aeneas massert (Primitives.lean
235–236); Rust describes the failed assertion as a panic. It differs from the
subnet unwrap branch, which the model classifies as `.panic`.

## Tagged mask conversion and with_netmask

For mask tag Vf with width w, define validMask(mask,p) by
p<=w AND value(mask)=2^w-2^(w-p). This predicate is independent of the parsing
algorithm. The public ip_mask_to_prefix normally returns Ok(p) iff this predicate
holds; Err PrefixLenError iff no such U8 p exists. Include every bit pattern,
zero mask, all-ones mask and every noncontiguous mask; accepted p is unique.
The ordinary Result is itself a normally successful computation.

IpNet::with_netmask(ip,mask) normally returns Ok of the EXACT original ip family,
stored address and parsed prefix p iff validMask(mask,p) and p<=width(ip).
It normally returns Err PrefixLenError iff no such p exists. No normalization
of host bits or implicit family equality condition. In particular:

* V6 address + valid V4 mask always accepts p in0..32 and returns V6.
* V4 address + valid V6 mask accepts exactly p in0..32 and returns V4;
  contiguous V6 masks p33..128 return Err.
* Either address tag + noncontiguous mask of either tag returns Err.
* Both zero masks accept /0 for either address tag.

Prove actual public dispatch/application bodies. Resolve any generated Lean
name shadowing through a precise extraction/naming compatibility correction;
do not replace application behavior with these desired formulas. Prior concrete
mask/with_netmask theorems remain the implementation bridge for same-family
cases, and actual IpNet::new supplies the cross-family prefix-width gate.

## Remaining coverage limits

These additions do not complete the crate. Actual aggregate for each concrete
family and IpNet remains outside accepted scope (sort plus mutable iteration,
merging and extension must compose); parser bodies retain the recorded borrowed
callback backend blocker. Display/Debug/Hash and optional serde/schemars bodies
and feature combinations remain unproved. Hash needs an explicit generic Hasher
state/effect contract rather than mere structural equality or an assumed digest.
Inherited iterator consumers and default comparison methods are not implied by
selected next/eq/cmp proofs. Known schema defects, heapless allocation behavior
and raw invalid-subnet prefix panic are already recorded, not new discoveries.

## Prospective global minimum subnet-count law

For width w in {32,128}, q<=w, and any raw endpoints 0<=s,e<2^w,
let I be empty if s>e, otherwise [s,e+1). Let G be a finite trace of the
actual corresponding subnet iterator from (s,e,q), including its final None.
For every finite competitor list C of (stored address a,p) pairs satisfying
0<=a<2^w, q<=p<=w, and a=lower(w,a,p), require:

    (forall x, x in I iff exists c in C, member(w,c.addr,c.prefix,x))
    implies G.length <= C.length.

The competitor may be unordered, overlapping or contain duplicate blocks;
length counts occurrences. Exact union (not merely covering I) is essential:
every competitor block must lie wholly within I. This containment may be an
explicit equivalent hypothesis if convenient. Empty I admits only an empty
competitor list because valid CIDR blocks are nonempty. No valid address or
prefix is excluded for representability of Nat cardinality or output count.

Prove a pure greedy-trace minimum theorem first, then compose it with the
checked actual-trace refinement. Largest eligible block at each step and exact
partition alone must not be reported as an already proved global minimum law.
A useful route is dyadic interval laminarity, global maximality of each greedy
block among canonical contained blocks with prefix>=q, and assignment of a
competitor list index covering each greedy start. No competitor can intersect
two distinct maximal greedy blocks; the assignment is injective. The resulting
law strengthens an existing iterator API's semantics, not the API-body count.
It does not assert allocation/collection success for enormous finite lists.

## PrefixLenError value traits

Source ipnet.rs122: PrefixLenError is a zero-field unit struct. If selected
actual derived bodies extract, Clone::clone normally returns exactly its input
for every value; PartialEq::eq normally returns true for every pair, equivalently
structural equality of this singleton type. A Unit extraction representation
must retain this singleton interpretation. These are two bodies; derived Eq
is a marker and Debug/Display formatting is separately excluded.

## AddrParseError value traits

Source parser.rs342–343 and public re-export lib.rs146: AddrParseError has
one Unit field and therefore one structural value. For every error e, actual
derived Clone::clone normally returns exactly e; for every pair a,b, actual
derived PartialEq::eq normally returns true. These two contracts concern the
exported error value alone. They do not establish any FromStr parser behavior,
error production condition, formatter behavior or successful parser extraction.
