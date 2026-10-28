# Frozen containment specification

Astra independent contract, 2026-10-16. The full user-supplied expert response
was provided as attachment `22b20f11-a1b7-40f3-ac15-78faf59d3f2a`.
Checked the pinned extraction Rust source (`nightly-2026-09-17`, core
`net/ip_addr.rs`: IPv4 comparison 1265–1300, segments 1525–1540, IPv6 comparison
2271–2306) and vendored ipnet 2.12.2 `Contains` implementations. Contracts below
are obligations, not claims of completion. Existing contracts remain unchanged.

## Independent interpretation and domain

Use `CidrModel.bytesValue`, the natural-number big-endian weighted octet sum,
and its `ipv4Value`/`ipv6Value` specializations. For a network with width `w`,
stored value `a`, and prefix `p`, use `K=2^(w-p)`, `lo=(a/K)*K`, `hi=lo+K-1`.
Its set is `{(family,x) | lo≤x ∧ x≤hi}`. These definitions must not call the
implementation under verification. IPv4 and IPv6 tags remain disjoint, including
IPv4-mapped IPv6. Valid networks require only `p≤w`; address bounds come from
their concrete octet type. All host bits, `/0`, `/w`, zero and MAX are included.
Both operands need validity for network containment. Raw structural equality
is distinct from equality of represented sets.

Every execution contract includes normal termination:
`∃ out, actual arguments = Aeneas.Result.ok out ∧ Post out`.
Shared inputs remain unchanged; if a generated signature returns state, that
state must preserve the input observations. No panic, failed indexing, or failed
conversion may be hidden by proving only an implication from success.

## IPv4 array/slice and ordering bridge

For any array `a:[T;N]`, the actual comparison-path conversion to slice `s`
must preserve `length(s)=N` and `∀i<N, s[i]=a[i]`, including order and shared
input contents. Record the exact Rust callee, LLBC types/trait dispatch, generated
Lean signature, model registration, and conversion placement. A typing repair
alone does not establish this content-preservation contract.

Let `V_B(ds)=Σi<N ds[i]*B^(N-1-i)`. For `B≥2`, equal length `N`, and all
`x[i],y[i]<B`, require full ordering equality
`lexCmp(x,y)=Nat.compare(V_B(x),V_B(y))`.
Use `(B,N)=(256,4)` for IPv4 and `(65536,8)` for IPv6. Prove all three Ordering
cases; neither equal-length nor digit-bound assumptions may be omitted.
Connect the actual selected slice/array comparison implementation or explicitly
record its reviewed model boundary, including any `compare_bytes` specialization.

For each address family, actual used comparison functions must satisfy:

| Function | Exact result |
| --- | --- |
| `cmp(a,b)` | `Nat.compare(value(a),value(b))` |
| `partial_cmp(a,b)` | `Some (Nat.compare(value(a),value(b)))` |
| `le(a,b)` | `decide(value(a)≤value(b))` |

The needed `le` path is mandatory. Do not claim unselected comparison methods
are verified just because the mathematical ordering lemma implies their expected
behavior. `partial_cmp` on the selected total-order types must never return None.

## IPv6 segments and byte order

For all 16 input octets `b`, `segments()` must return exactly eight U16 values
with `s[i].val=256*b[2*i].val+b[2*i+1].val` for every `i<8`.
Prove `V_65536(s)=V_256(b)`. This is a numeric correspondence, not equality to
host-endian bytes. No byte-pattern preconditions are allowed.

Pinned Rust first transmutes `[u8;16]` by value to `[u16;8]`, then applies
`u16::from_be` to each element. There are two acceptable boundaries:

1. Model/extract raw transmute using native endian: on little endian its element
   is `b[2i]+256*b[2i+1]`; on big endian it is `256*b[2i]+b[2i+1]`. Compose with
   the actual `from_be` conversion.
2. Model `Ipv6Addr::segments` as a whole using the big-endian pair formula above.

The accepted implementation choice may instead place the reviewed trusted boundary
at the entire concrete `Ipv6Addr::cmp`: numeric comparison of the same 16
big-endian octets. In that case the full segments/endian/lexicographic chain above
is part of the explicitly unproved Rust/model correspondence; it is not reported
as an independently verified `segments()` implementation. This changes the
location and classification of trust, not the containment domain or postcondition.
The same classification applies to a concrete IPv4 comparator model.

Do not model raw transmute as big-endian and retain a later little-endian swap.
For the raw operation record equal 16-byte sizes, contiguous array element
layout, initialized bits, valid integer bit patterns, and target endian. This
by-value operation does not require equal source/target alignments. Do not
introduce a generic transmute model when only this concrete operation is needed.

## Exact containment completion unit

Require the following six actual `Contains` trait implementations, plus the six
corresponding public generic method specializations using their real dictionaries:

| Receiver | Operand | `out=true` iff |
| --- | --- | --- |
| `Ipv4Net` | `&Ipv4Addr` | `lo(n)≤value(a) ∧ value(a)≤hi(n)` |
| `Ipv6Net` | `&Ipv6Addr` | same at width 128 |
| `Ipv4Net` | `&Ipv4Net` | `S(m)⊆S(n)` |
| `Ipv6Net` | `&Ipv6Net` | `S(m)⊆S(n)` |
| `IpNet` | `&IpAddr` | `(family(a),value(a))∈S(n)` |
| `IpNet` | `&IpNet` | `S(m)⊆S(n)` |

Network inclusion must be connected by a checked theorem to
`sameFamily ∧ lo(n)≤lo(m) ∧ hi(m)≤hi(n)`. All sets are nonempty, so differing
families yield false, including `/0`. The two enum implementations must cover
both same-family branches and both mismatches. Generic-wrapper proofs must
name the built-in trait instances, not assume an arbitrary instance is correct.
Count inherent APIs, instantiations, trait implementations and helper lemmas
separately in inventory. Trait-only proofs do not complete public-wrapper coverage.

Derived reflexivity/transitivity, normalization invariance and mutual inclusion
may be added after composition. Mutual inclusion gives equality of canonical
representations, not raw stored addresses. This completion unit requires all six
rows, public connections, full valid/noncanonical domains, total success and
exact decisions, audited dependencies, and the boundary ledger below. A completed
IPv4 subset may be reported explicitly while IPv6 remains unfinished.

## Evidence and permitted trust

The user now permits small reviewed standard-library models when extraction
would unnecessarily expand the unsafe scope. This does not authorize application
axioms, changed ipnet bodies, handwritten generated output, or stronger input
preconditions. Prefer a supported connection fix, then narrow extraction, then
an explicitly reviewed concrete model. Follow `model-boundaries.md`: Lean model
correctness and Rust/model correspondence are separate claims. A successful axiom
audit does not establish the latter.

Connection-focused native examples: `1.0.0.0 > 0.255.255.255`, IPv6
`00ff:ffff:ffff:ffff:ffff:ffff:ffff:ffff < 0100::`, bytes `01..10` mapping to
segments `0102,0304,...,0f10`, and noncanonical `10.0.0.1/24` endpoint membership.
These detect wiring/endian mistakes and do not replace universal theorems.
