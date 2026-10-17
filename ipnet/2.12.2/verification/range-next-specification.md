# Frozen IPv4 range-next specification

Independent Astra contract, 2026-10-16, following expert-contains-review.txt §3.1.
This is the next completion unit after accepted containment evidence
`check-bjEjjfsA`; it does not change or extend that historical evidence. Checked
vendored `upstream/src/ipext.rs`: raw range fields/new (327/374), `IpStep` IPv4
methods (235–246), and `Iterator for Ipv4AddrRange::next` (476–490).

## Domain and independent state interpretation

Include **every** raw `Ipv4AddrRange {start,end}` state: no ordering, nonempty,
constructor-history, or nonmaximum-address hypothesis is permitted. Define
`s = CidrModel.ipv4Value start`, `e = CidrModel.ipv4Value end` in `Nat`.
Their bounds `s,e < 2^32` follow from the concrete four-octet type.

The independent remaining-state model is:

```
remaining(r) = Empty            if s > e
             = Live(s,e+1)     if s ≤ e
```

`Live(s,t)` denotes the half-open natural-number interval `[s,t)` and satisfies
`0≤s<t≤2^32`. Define remaining size as zero for Empty, `t-s` for Live.
All arithmetic in this specification is unbounded `Nat`; notably the full range
has upper endpoint and length `2^32`. The model does not call any extracted
iterator, comparison, or arithmetic method.

Empty concrete states need not have identical fields: all reversed intervals
have the same abstract meaning. A proof may establish stronger exact fields,
but abstract equality is enough. The existing raw constructor storage contract
must connect `new(start,end)` to this interpretation for all endpoint pairs.

## One-step public contract

For the **actual generated** `Ipv4AddrRange` implementation of `Iterator::next`,
require existence of both returned option `out` and updated state `r'` such that
execution terminates with normal outer Aeneas success and simultaneously:

| Initial remaining state | Returned option | Updated remaining state |
| --- | --- | --- |
| Empty | None | Empty |
| Live(s,t), s+1=t | Some address a, `ipv4Value(a)=s` | Empty |
| Live(s,t), s+1<t | Some address a, `ipv4Value(a)=s` | Live(s+1,t) |

State order in the theorem must match the actual generated mutable-call signature,
rather than assuming an `(out,state)` convention before inspecting it. If Aeneas
returns a state-reconstruction function, specify application to the caller's
updated range and prove that the reconstructed range has the stated meaning.
Returned value alone is insufficient. No implication conditioned on successful
execution may replace the required total-success equality.

This immediately requires `out=None ↔ remaining(r)=Empty`. For Some, the returned
value is exactly the initial least member, and the old remaining set is the
**disjoint** union of that singleton and the new remaining set. The remaining
size decreases by exactly one. For None it stays zero. Prove these as derived
laws or state them in the combined contract, with dependencies on the actual
next-body theorem. No model-only transition law counts as public API coverage.

## Boundary obligations and exhaustion

The universal theorem must include reversed endpoints, `[0,0]`, `[MAX,MAX]`,
`[0,MAX]`, and ordinary singleton/multiple-address ranges. In particular:

- `[0,0]` returns zero once and becomes empty, never `[0,0]` again.
- `[MAX,MAX]` returns MAX once and becomes empty without relying on `MAX+1`
  fitting an address.
- `[0,MAX]` returns zero and leaves `[1,2^32)` in the mathematical model.
- Reversed endpoints return None and remain abstractly empty.

From empty preservation, show a second next call after None also returns None
and remains empty. A finite number of further next calls cannot revive elements.
A repeated-next corollary may show exact ascending contents and termination after
the initial Nat length, but does not claim allocation/collection of a complete
Rust vector succeeds. `next_back`, skips, count, IPv6, enum wrappers, hosts,
subnets, and aggregate remain separate completion units.

## Source-to-proof plan and allowed boundaries

The pinned source first calls `partial_cmp(start,end)`. For Less it computes
`start.add_one()` then replaces start while returning its old value. Since
`s<e<2^32`, that increment is in range and any saturating arithmetic equals
ordinary `s+1`; prove this from the branch condition rather than adding a public
precondition. End is preserved. For Equal it replaces end by zero and start by
one, returning the old start: `(1,0)` is empty even at initial zero or MAX.
The other branch returns None. The comparison bridge's total Some result rules
out a spurious None comparison branch for addresses.

Reuse accepted address-value conversion and reviewed concrete comparator/type
boundaries. If additional standard-library operations need modeling, prefer
existing supported models or narrow extraction; record any new reviewed-trusted
correspondence in model-boundaries.md. For `mem::replace`, require the exact
returned old value and updated new value. For address construction from four
bytes, require the exact four input octets. For U32 saturating addition, require
`val(result)=min(val(x)+val(y),2^32-1)` over all scalar inputs. These are helper
contracts, not permission to replace the ipnet next body with the desired model.

Completion requires the combined returned-value/state contract, empty preservation
and no revival, all raw endpoint domains, a connection from the actual selected
Iterator implementation, updated theorem/API inventory, reviewed model boundaries,
and a reproducible full build/axiom audit/fingerprint check. Native boundary cases
supplement this evidence and must be reported separately.
