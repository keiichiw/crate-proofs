# CIDR set and iterator contracts

Independent Astra extension, 2026-10-16. This is a specification, not evidence
that the implementations satisfy it. The existing 15 constructor/observer
contracts in `specification.md` remain unchanged. This document refines the
extension obligations there; any counterexample must be recorded rather than
removed by narrowing the input domain.

## Representation and independent model

For width `w = 32` or `128`, an address is exactly `w/8` octets. Define
`val(bytes) = Σ i < w/8, bytes[i] * 256^(w/8-1-i)` in `Nat`.
Prove `val < 2^w`, injectivity for fixed width, and agreement of generated
address/integer conversions with this definition. IPv6 segments, where needed,
are big-endian pairs of octets. Host machine endianness must not change `val`.
Tagged addresses are `(V4,val)` or `(V6,val)`; IPv4-mapped IPv6 stays V6.
No address model is defined by calling `network`, `broadcast`, or `contains`.

A valid network has stored address `a` and `u8` prefix `p ≤ w`. All addresses
are permitted, including nonzero host bits. Let
`K = 2^(w-p)`, `lo = (a/K)*K`, `hi = lo+K-1` in `Nat`.
Define `S(n) = { (family(n),x) | lo(n) ≤ x ∧ x ≤ hi(n) }`.
Prove `lo ≤ a ≤ hi < 2^w`; `/0` and `/w` are included. Structural equality
observes original address and prefix; set equality forgets host bits.
For two valid networks, set equality is equivalent to equality of family,
prefix, and `lo`, not necessarily equality of their stored Rust values.

Every ordinary-success theorem includes `∃ out, actual args = Result.ok out ∧
Post out`. Mutable methods must additionally specify returned updated state.
A Rust error is an ordinary output. A panic-domain theorem is separate and
states the actual modeled failure; it never asserts ordinary total success.

## First major target: contains

The public generic methods must be instantiated with their actual trait
dictionaries. Cover these six `Contains` implementations and their corresponding
public method applications:

| Receiver | Operand | Boolean postcondition |
| --- | --- | --- |
| `Ipv4Net` | `&Ipv4Addr` | `lo(n) ≤ val(x) ∧ val(x) ≤ hi(n)` |
| `Ipv6Net` | `&Ipv6Addr` | same at width 128 |
| `Ipv4Net` | `&Ipv4Net` | `S(m) ⊆ S(n)` |
| `Ipv6Net` | `&Ipv6Net` | `S(m) ⊆ S(n)` |
| `IpNet` | `&IpAddr` | `(family(x),val(x)) ∈ S(n)` |
| `IpNet` | `&IpNet` | `S(m) ⊆ S(n)` |

Require exactly `out = true ↔ predicate`, with total success, for valid receiver
and (for network operands) valid operand. No alignment hypotheses. Different
families always yield false, even for `/0`. The six cases are not six independent
new inherent APIs: inventory must distinguish trait bodies and specialized public
dispatch, without inflating API coverage.

The critical bridge for network operands is
`S(m) ⊆ S(n) ↔ sameFamily ∧ lo(n) ≤ lo(m) ∧ hi(m) ≤ hi(n)`.
All valid CIDR sets are nonempty, making cross-family subset false. Merely
checking the stored operand address is not sufficient. Derived consumer laws:
reflexivity, transitivity, invariance under `trunc` on either network, and mutual
containment iff their canonical representations agree. These laws count as
implementation guarantees only after connection to actual generated methods.

## Concrete proof sequence

1. Give concrete generated octet structures the `val` interpretation. Prove
   address/integer conversion and comparison bridges. Independently prove the
   interval/subset lemma above, retaining separate helper status in inventory.
2. Extract and prove `netmask`, `hostmask`, `network`, `broadcast` for each width:
   returned numeric values are `2^w-K`, `K-1`, `lo`, `hi`, respectively.
   Include address bitwise operators and conversion dependencies as needed.
3. Compose those bridges through each concrete generated `Contains` body, then
   tagged dispatch and actual public generic method instantiations. Audit the
   full dependency chain. This completes the first major target.
4. Prove `trunc`, `supernet`, and `is_sibling` against the existing contracts;
   use canonical inequality, not raw value inequality, for sibling-union laws.
5. Proceed to range transitions, arbitrary-interval subnet transitions, and
   aggregate union preservation below. Allocation and platform bounds must be
   explicit where relevant.

An independently useful small extension during arithmetic extraction work is
exact storage contracts for the four raw `AddrRange::new`/`Subnets::new`
constructors and tag-preserving conversions. It does not complete containment.
Individual extraction probes must identify which concrete dependency fails;
never classify all untried APIs as blocked. Compiler MIR selection or a supported
standard-library model is acceptable only with recorded options/model boundary,
unchanged source/pins, regenerated files, and axiom audit. Handwritten replacement
implementation bodies and application axioms are not acceptable bridges.

## Raw range states and hosts

A raw address range consists of any two width-bounded addresses `(s,e)`.
`R(s,e)` is the ascending inclusive sequence `s,...,e` when `s≤e`, otherwise
empty. Its mathematical length is `L = if s≤e then e-s+1 else 0` in `Nat`.
All raw states are included; `new(s,e)` returns exactly those fields.
Different concrete empty states may denote the same empty sequence.

| Method | Returned value | Updated abstract sequence |
| --- | --- | --- |
| `next` | head or `None` | drop one from front |
| `next_back` | last or `None` | drop one from back |
| `nth(k)` | zero-based front element `k`, or `None` | drop `min(L,k+1)` from front |
| `nth_back(k)` | zero-based back element `k`, or `None` | drop `min(L,k+1)` from back |
| `last`, `max` | last or `None` | receiver consumed |
| `min` | head or `None` | receiver consumed |
| `count` | `L`, provided `L ≤ usize::MAX` | receiver consumed |
| `size_hint` | `(L,Some L)` if `L≤usize::MAX`, else `(usize::MAX,None)` | unchanged |

Here `k+1` is mathematical addition, including `k=usize::MAX`; full IPv6 length
is `2^128`. Do not require either to fit a Rust scalar. `count` outside its
stated bound needs a separate platform/overflow-mode contract. `size_hint`
and the other state operations retain the full range domain. Enum wrappers
preserve tags and abstract remaining sequence. Empty states never revive under
any mixture of front/back/skip operations. Prove that returned, skipped and
remaining elements partition the original sequence without repetition.

For `hosts`, initialize this range with `[lo+1,hi-1]` for IPv4 `p<31`, and
`[lo,hi]` for IPv4 `p≥31` and all IPv6 prefixes. In particular `/31` gives two
IPv4 addresses and `/32` one. Constructors and subsequent iterator transitions
are separate composable contracts.

## Subnet states and partition

`Ipv4Subnets::new(s,e,q)` and `Ipv6Subnets::new(s,e,q)` accept all addresses and
all `u8 q`, terminate normally, and store the exact arguments. They do not
validate `q`. Model the remaining interval by `R(s,e)` with additional minimum
prefix `q`; no canonical alignment condition on `s` is allowed.

For `next`, if `s>e`, return `None` and preserve the empty state for every `q`.
For nonempty states and `q≤w`, choose the greatest natural `h` satisfying
`h≤w-q`, `2^h divides s`, and `s+2^h-1≤e`.
The set of candidates is finite and contains zero. Return exactly the canonical
network with stored address `s` and prefix `w-h`. Updated abstract interval is
`[s+2^h,e]`, or empty if `s+2^h>e`. Mathematical endpoints may equal `2^w`;
the concrete state must encode exhaustion without wrapping or repeating MAX.
The minimum prefix is preserved. This proves strict decrease of remaining
cardinality, exact coverage, disjointness, ascending order and per-step maximality.
For nonempty raw states with `q>w`, specify modeled panic separately, reflecting
the internal failed constructor unwrap; do not claim total-success enumeration.

For valid network `n`, `n.subnets(q)` returns Rust `Err PrefixLenError` exactly
when `q<p` or `q>w`, and otherwise constructs an iterator whose complete sequence
has length `2^(q-p)` with element `i` exactly `(lo(n)+i*2^(w-q),q)` for
`i<2^(q-p)`. All outputs have the same family. In particular `q=p` produces
`[trunc(n)]`. Prove output union `S(n)`, pairwise disjointness, and exhaustion.
No theorem needs to allocate the complete mathematical sequence.

## Aggregate

For each finite machine-representable list of valid networks, including empty,
duplicate, noncanonical and mixed-family inputs where the API accepts them,
require total success and `∀ x, (∃ n∈output, x∈S(n)) ↔ (∃ n∈input, x∈S(n))`.
Require valid canonical outputs, pairwise disjoint sets for distinct positions,
and the actual documented output ordering once separately specified/proved.
Do not silently assert unlimited allocation succeeds: record the extraction's
allocation model and any unavoidable representability limits explicitly.

Prove in stages: network-to-interval correspondence; sorting as a permutation;
overlap/adjacency merge preserves union; greedy subnet decomposition preserves
each merged interval; compose through actual aggregate bodies. Follow with
idempotence, permutation/duplicate invariance, maximal CIDR blocks, uniqueness
and minimum output count. These later normal-form claims are separate obligations.
Universal domains must include MAX-1 singleton inputs, MAX endpoints, `/0`,
`/w`, contained networks, and adjacent intervals that are not one CIDR.
Native regressions for these cases supplement, and never replace, the proofs.

## Expert guidance provenance

The full user-provided Japanese expert attachment was read on 2026-10-16:
`/Users/keiichiw/.codex/attachments/5dbb32e1-940a-45cc-bd04-e0bd8f7a4673/貼り付けたテキスト.txt`.
It recommends containment first, then exact partition/aggregation, and supplies
range-state and schema counterexample guidance. This specification independently
checks the relevant definitions and state domains against the unchanged vendored
2.12.2 source. The attachment's claims are guidance, not proof evidence or a
substitute for checking generated source and theorem dependencies. Schema
counterexamples and prospective upstream bug reports are tracked separately;
no publication is authorized here.
