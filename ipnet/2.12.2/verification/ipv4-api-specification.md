# Frozen IPv4 API expansion contracts

Independent Astra specification, 2026-10-16. Baseline: 196 audited theorems / 43
API entries in accepted `check-X7MRKMCv`. This document defines new obligations,
not completed coverage. Read against unchanged `upstream/src/ipext.rs` IPv4 range
methods and `upstream/src/ipnet.rs` IPv4 network methods. Existing independent
CIDR and range models remain authoritative; no input alignment is assumed.

## Scope and priority

First extend the actual IPv4 range observers and back/skip operations, and the
network constructors/observers that compose existing boundary proofs. Then
`supernet`, `is_sibling`, and `subnets` construction. Treat `with_netmask` as a
separate optional completion unit if exact mask parsing extracts. No generic
unsafe or sorting support is prerequisite for this batch. Defer individual
blocked APIs explicitly rather than weakening their contract or blocking all
independent APIs. No claim about IPv6, arbitrary target platforms, subnet
iteration, or collection follows from these contracts.

## Common domains and success convention

For any raw IPv4 range, set `s=ipv4Value(start)`, `e=ipv4Value(end)`, and
`remaining=Empty` if `s>e`, otherwise `Live(s,e+1)`. Its Nat length `L` is zero
or `e+1-s`. All raw endpoint pairs are included. Let `M=2^32-1`.
For a valid IPv4 network let `a=ipv4Value(addr)`, `p=prefix_len.val≤32`,
`K=2^(32-p)`, `lo=(a/K)*K`, `hi=lo+K-1`. All original host bits are allowed.

Every selected actual generated API must terminate normally:
`∃ output, actual(input)=Aeneas.Result.ok output ∧ Post`.
For mutable range methods include updated range `r'` in that same theorem and
observe its remaining state. Rust `Err PrefixLenError` is an ordinary successful
outer result. Error branches must be exact. Shared inputs are preserved.

The accepted target has 64-bit `usize`, checked through `toolchain.json` and
`check-tools.py`. Therefore every IPv4 range length `L≤2^32` fits `usize`.
There is **no range-length restriction** on IPv4 count/size_hint on this target.
Do not generalize this claim to 32-bit `usize`: a full IPv4 range has length
`2^32` and would not fit. For skip index `k=usize.val`, include all
`0≤k≤2^64-1`; do not assume `k` fits U32. The Rust `usize as u64` cast is exact
on the selected platform. Intermediate `k+1` in specifications is Nat arithmetic.

## Raw range back and skip methods

Read length-zero half-open intervals as Empty.

| API and old state | Result | New remaining state |
| --- | --- | --- |
| `next_back`, Empty | None | Empty |
| `next_back`, Live(s,t) | Some a with value `t-1` | `[s,t-1)` |
| `nth(k)`, `k<L` | Some a with value `s+k` | `[s+k+1,t)` |
| `nth(k)`, `k≥L` | None | Empty |
| `nth_back(k)`, `k<L` | Some a with value `t-1-k` | `[s,t-1-k)` |
| `nth_back(k)`, `k≥L` | None | Empty |

Here nonempty skip rows use `remaining=Live(s,t)`; the `k≥L` rows include Empty.
The returned and skipped elements are consumed. Endpoints outside the remaining
interval must not be returned. The last surviving address is returned once and
leaves Empty, including 0 and MAX singletons. Empty concrete sentinels need not
be structurally identical. Actual back/skip exhaustion must remain empty under
further selected front/back/skip operations. Useful derived laws are
`nth(0)=next` and `nth_back(0)=next_back` in both return and abstract state, and
partition of the old interval into skipped, returned, and remaining elements.

The implementation has three skip branches: `k≥L`, `k=L-1`, and `k<L-1`.
Only the final branch casts `k` to U32 for arithmetic. Prove from that branch
`k<2^32`, and that the added/subtracted value and subsequent one-step update are
in range. Do not insert those bounds into the public contract. `count_u64` is a
helper with exact Nat value `L` and total success on all raw endpoints.

## Raw range observations and consuming methods

| API | Exact ordinary output on the selected 64-bit target |
| --- | --- |
| `count` | Usize whose value is `L` |
| `size_hint` | `(L,Some L)` represented exactly as Usize; shared state unchanged |
| `last` | None iff Empty; otherwise Some address with value `t-1` |
| `max` | same as last |
| `min` | None iff Empty; otherwise Some address with value `s` |

Consuming methods do not return a live receiver and need no post-consumption
state. These APIs must cover full `[0,MAX]`, all singletons and every reversed
pair. A portable size_hint extension would be `(min(L,U), if L≤U then Some L
else None)`, where `U=usize::MAX`; that extension is not implied by a fixed64
proof. For portable count, require `L≤U` separately and specify larger-range
panic/overflow behavior under a fixed configuration before claiming it.

## Network-derived ranges and basic constructors

`Ipv4Net::hosts(n)` for every `p≤32` returns an actual raw range whose independent
remaining state is `[lo+1,hi)` for `p<31`, otherwise `[lo,hi+1)`. Thus `/31`
returns both addresses and `/32` its single address. Exact raw numeric endpoints
are `lo+1,hi-1` or `lo,hi`, respectively. Prove the p<31 adjustments do not
saturate from the network-size facts. Subsequent enumeration correctness is
composition with actual range operations, not automatic success of Vec collect.

`Default for Ipv4Net` returns exactly numeric address zero and prefix zero,
representing the entire IPv4 address set. It is not an empty range/network.
`From<Ipv4Addr> for Ipv4Net` returns exactly the original stored address and
prefix 32, for every address, and denotes its singleton. Preserve structural
address equality in the primary constructor contract, not just membership.

## Supernet and sibling

For every valid n, `supernet` returns None iff `p=0`; otherwise Some t with
`t.prefix_len=p-1` and `ipv4Value(t.addr)=lower(32,a,p-1)`. The parent is
canonical, valid and contains `S(n)`. `/0` uses wrapping prefix subtraction in
the source but must still terminate and return None; do not restrict to p>0.

For both valid networks n,m, `is_sibling` returns a Boolean equivalent to:

```
p_n > 0 ∧ p_n = p_m ∧
lower(32,a_n,p_n-1) = lower(32,a_m,p_m-1)
```

This means equal immediate parent sets. Pinned implementation checks positive
prefix, equal prefixes, then whether the first network's parent contains the
second. The equal-parent characterization must be derived, not presumed from
the method name. A parent-containment formulation is an acceptable intermediate
but must be connected to the independent parent-set condition before completion.
The API permits a network to be its own sibling for p>0. It also permits unequal
stored addresses with equal CIDR sets. Therefore merging siblings preserves
union only with the additional condition that their canonical child blocks are
distinct; raw n≠m is not sufficient. `/0` sibling returns false without panic.

## Network subnets construction, not iteration

For valid n and **all** U8 q, `Ipv4Net::subnets(q)` returns exactly
Rust `Err PrefixLenError` iff `q<p` or `q>32`; otherwise Rust Ok raw iterator
with numeric start `lo`, end `hi`, and exact stored minimum prefix q.
Ordinary outer execution succeeds for every q. This creates the correct initial
state but does not prove `Ipv4Subnets::next`, fixed-q enumeration, coverage, or
aggregation. Keep constructor-only API descriptions explicit.

When iteration is later proved, public network subnets must produce exactly
`2^(q-p)` canonical `/q` blocks at `lo+i*2^(32-q)`, including `[trunc(n)]` when
q=p. This later obligation may not be weakened to arbitrary smaller blocks.

## Optional mask construction unit

Define `validMask(m,p) := p≤32 ∧ ipv4Value(m)=2^32-2^(32-p)` independently.
For every mask address, `ipv4_mask_to_prefix` returns Rust Ok p exactly when
validMask(m,p); otherwise exactly Err PrefixLenError, with ordinary outer
success in both cases. Valid p is unique. Include all-zero (/0), all-one (/32),
and every noncontiguous mask as well as contiguous intermediate prefixes.

`Ipv4Net::with_netmask(ip,m)` preserves the exact original ip (all host bits),
returns Rust Ok network with prefix p exactly for validMask(m,p), otherwise
Err PrefixLenError. It takes no input alignment assumption. Parsing the mask's
leading ones and checking the remaining bits must connect to this independent
formula; examples alone do not prove rejection of every hole. This specific
IPv4 API has no cross-family parameter. Do not import a family-equality rule
into the separate IpNet API, which permits some mixed-family inputs.

## Evidence and boundary discipline

Reuse reviewed address/comparator representations and existing scalar/memory
models. New helper lemmas about a model do not prove its Rust correspondence.
Record newly selected std operation models and exact concrete type boundaries
in model-boundaries.md; prefer narrow existing models over new hand-written
models. Never edit generated bodies. Tests target boundary connection mistakes;
formal inventory names only actual completed contracts, with platform scope and
constructor-versus-iterator distinction. Preserve accepted historical evidence.

## Public IPv4 saturating arithmetic traits

The source macros in `upstream/src/ipext.rs:155–190` define exactly one IPv4
addition overload and two subtraction overloads. With `A=ipv4Value(a)`,
`B=ipv4Value(b)`, scalar value `d`, and `M=2^32-1`, require:

| Public trait specialization | Rust output type | Exact mathematical output |
| --- | --- | --- |
| `<Ipv4Addr as IpAdd<u32>>::saturating_add(a,d)` | `Ipv4Addr` | address value `min(A+d,M)` |
| `<Ipv4Addr as IpSub<u32>>::saturating_sub(a,d)` | `Ipv4Addr` | address value `A-d` (Nat truncated subtraction) |
| `<Ipv4Addr as IpSub<Ipv4Addr>>::saturating_sub(a,b)` | `u32` | scalar value `A-B` (Nat truncated subtraction) |

Each contract quantifies over every address and every corresponding RHS input,
includes ordinary outer success, and imposes no no-overflow/no-underflow
precondition. Zero and MAX on either side are included. No wrapping arithmetic,
signed distance, absolute difference, or address return for the address-address
subtraction is intended. There is no IPv4 `IpAdd<Ipv4Addr>` overload in this
source; do not infer one from the trait's default generic parameter.

The full existing `RangeNext.ipv4_saturating_add_spec` is eligible to support the
first public mapping if it targets the actual extracted trait method and passes
the same audit as other API contracts. Full-domain subtraction helpers are
likewise eligible when they state the actual methods and the corresponding
return types above. Label all three mappings with the RHS specialization;
model-level U32 arithmetic lemmas and the internal `IpStep` methods remain
helpers rather than extra public API coverage. This promotion changes inventory
classification only when the full public contract was already established; it
must not multiply counts for helper names or generic trait declarations.


## Public IPv4 bitwise traits

The `ip_bitops_impl!` expansion in `upstream/src/ipext.rs:193–222` and
public re-export in `src/lib.rs` select four IPv4 specializations. For every
address `a`, address `b`, and U32 scalar `d`, let `A=ipv4Value(a)`,
`B=ipv4Value(b)` and `D=d.val`. Address values use the independent big-endian
weighted-octet interpretation, irrespective of native machine byte order.

| Public trait specialization | Rust output | Exact output address value |
| --- | --- | --- |
| `<Ipv4Addr as IpBitAnd<Ipv4Addr>>::bitand(a,b)` | `Ipv4Addr` | `Nat.land A B` |
| `<Ipv4Addr as IpBitAnd<u32>>::bitand(a,d)` | `Ipv4Addr` | `Nat.land A D` |
| `<Ipv4Addr as IpBitOr<Ipv4Addr>>::bitor(a,b)` | `Ipv4Addr` | `Nat.lor A B` |
| `<Ipv4Addr as IpBitOr<u32>>::bitor(a,d)` | `Ipv4Addr` | `Nat.lor A D` |

Each actual method must return ordinary outer success and exactly that address
value, without restrictions on input patterns. Equivalently, every bit index
0 through 31 is the conjunction/disjunction of the corresponding input bits,
and all higher bits are zero. Scalar RHS values are numeric values, not native
memory byte sequences. These contracts include zero, MAX, alternating bits and
arbitrary non-mask operands. No generic trait declaration or scalar-model lemma
is an additional verified public overload. Coverage remains contingent on the
actual extracted-method proof and final audit.
