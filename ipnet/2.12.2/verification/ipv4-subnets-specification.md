# Independent IPv4 subnet enumeration specification

Astra oracle specification, 2026-10-16, for ipnet 2.12.2. This document is a
contract target, not completed proof evidence. Source inspected:
`upstream/src/ipnet.rs:1523–1650` and the actual `Ipv4Subnets::next` body.
Use the existing independent big-endian octet value and CIDR set definitions.
No generated implementation operation defines the mathematical choice below.

## Raw state and domain classification

A state contains any addresses start/end and any U8 minimum prefix q. Let their
values be s,e,q. Interpret remaining addresses as Empty if s>e, otherwise the
Nat half-open interval [s,e+1). Keep q as a separate observable. Endpoint e+1
may equal 2^32; it is not a machine address. `new` normally returns the exact
three supplied fields, without validating q.

For empty states, `next` normally returns None and leaves the remaining interval
empty for every q in 0..255. For nonempty states q≤32, require total normal
success with the output and updated state specified below. For nonempty states
q>32, require a separate modeled failure/panic theorem: the actual helper selects
a prefix at least q, `Ipv4Net::new` returns Err, and unwrap panics. Do not assert
ordinary total success on this domain, nor silently exclude it from the domain
classification. The public constructor has no explicit validation or documented
Panics section; q≤32 is the mathematical admissibility condition, not a claimed
source-enforced invariant. Panic implementation dependencies may need separate
extraction evidence; failure is not an ordinary PrefixLenError result of next.

## One-step mathematical choice

For s≤e and q≤32 define the finite nonempty candidate set

    H(s,e,q) = { h : Nat | h≤32-q ∧ 2^h divides s ∧ s+2^h≤e+1 }.

Let h be its greatest element, K=2^h, and p=32-h. Zero is always a candidate.
The exact returned network has stored address equal to the original start
address and prefix p. In particular its stored address is canonical, p≥q,
and its set is exactly [s,s+K). The updated state preserves q and represents
[s+K,e+1) when s+K<e+1, otherwise Empty. Require this normal result and state
relation in the same theorem about the actual extracted call.

Concrete empty encodings may differ; do not require a particular sentinel.
The mathematical update never wraps at MAX. Singleton zero, singleton MAX,
full range [0,2^32), arbitrary unaligned s, q=0 and q=32 are included. For
example full range with q=0 returns 0.0.0.0/0 then exhausts; q=32 always
returns the singleton at s. The raw input interval need not itself be a CIDR.

## Derived obligations and composition

Prove the selected network is valid/canonical and its addresses, together with
the updated remainder, form a disjoint exact partition of the original interval.
On Some, the Nat remaining length decreases by K≥1. On None, the original
remaining interval is empty. Empty states do not revive under repeated next.
The greatest-h condition establishes per-step maximality: no larger aligned
CIDR starting at s and respecting q fits inside the original remaining interval.
It is not merely a claim that the selected block happens to fit.

Connect the total transition to a finite trace relation of actual next calls:
for admissible initial states, termination requires at most the initial Nat
length successful calls, followed by None. Outputs are canonical, in increasing
address order, pairwise disjoint, and their union is exactly the initial interval.
The decreasing measure is Nat, so a full-range length 2^32 needs no usize or U32
representation assumption. Do not claim a concrete allocated vector of that
length exists or can be collected successfully.

For a valid possibly noncanonical network n with prefix p, and p≤q≤32,
compose the already verified `n.subnets(q)` constructor with next. Put
lo=lower(n), K=2^(32-q), N=2^(q-p). Its successful output at index i<N is
exactly the canonical network (lo+i*K,q); after N outputs it is exhausted.
This fixes the prefix for this constructor-originated enumeration, although
arbitrary raw intervals generally yield varying prefixes. In particular q=p
returns exactly trunc(n) once. Prove output set partition and count N through
the actual trace, without requiring an allocated list. Existing ordinary error
cases q<p or q>32 remain part of the constructor contract.

## Later aggregate and parser work

`Ipv4Net::aggregate` requires all valid input networks, including duplicates and
noncanonical addresses. Independent target: canonical ascending disjoint CIDRs
with exactly the input set union, and no pair whose union is one CIDR. Its source
forms numeric intervals, sorts, merges overlapping/adjacent intervals, and
extends each with raw subnets minimum prefix zero. Prove each composition step;
source ordering or a successful sort call alone does not establish a permutation.
Allocation/Vec length limits must remain explicit model boundaries. Saturated
adjacency at MAX is mathematically harmless because no IPv4 start exceeds MAX.
No new aggregate bug has been established by this source review.

The IPv4 FromStr grammar should be specified independently as exactly four
ASCII decimal components, each 1..3 digits with numeric value ≤255, separated
by literal '.', then literal '/', then 1..2 ASCII decimal digits with value
≤32, and EOF. This implementation accepts leading zeros in either component
or prefix. It accepts no whitespace, sign, missing slash, trailing bytes or
non-ASCII digits. Store the parsed original address without truncating host
bits. All other UTF-8 strings return the ordinary parse error; parser cursor
rollback and overflow bounds must be proved for the actual byte-level body.
A difference from another library's grammar alone is not a demonstrated bug.
Parser and aggregate are later targets, not covered by subnet-transition proofs.
