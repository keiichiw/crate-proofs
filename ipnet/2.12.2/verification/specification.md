# Independent specification for ipnet 2.12.2

Authored by the Astra specification agent on 2026-10-16, before implementation
proofs. Sol owns implementation proofs; Astra may explain or review this contract
as an oracle. This document defines obligations, not completed verification.
Completed coverage must be established separately by the audited theorem inventory.

The independent [CIDR set and iterator contracts](set-operations-specification.md)
refine the extension roadmap following the full expert guidance supplied on
2026-10-16. Containment is the next major goal, followed by exact range state
transitions, subnet partition, and aggregation union preservation. They do not
change the 15 constructor/observer contracts or claim additional proved APIs.

## Mathematical observations

An address of width `w ∈ {32, 128}` denotes a natural number `a < 2^w` in
network byte order. Its octets denote `Σᵢ octet[i] * 256^(w/8-1-i)`.
A network value denotes `(w, a, p)`, with `0 ≤ p ≤ w`. In particular **`a`
need not be a network boundary**: constructors preserve host bits. IPv4 and
IPv6 are disjoint tagged domains, including IPv4-mapped IPv6 addresses.

For valid `p`, independently define in natural-number arithmetic:

```
size(w,p)       = 2^(w-p)
hostmask(w,p)   = size(w,p)-1
netmask(w,p)    = 2^w-size(w,p)
lower(w,a,p)    = (a / size(w,p))*size(w,p)
upper(w,a,p)    = lower(w,a,p)+size(w,p)-1
members(w,a,p)  = { x | lower(w,a,p) ≤ x ∧ x ≤ upper(w,a,p) }
```

Division is natural-number division. These definitions use unbounded arithmetic;
in particular `size(w,0)=2^w` need not fit a Rust integer. Public proofs must
establish implementation safety, not add a restriction excluding `/0`.
Network representation equality observes the stored address and prefix, while
equality of `members` observes only the represented address set.

## Success and error convention

For each selected generated body `f`, require
`∃ out, f input = Aeneas.Result.ok out ∧ Post(input,out)`.
This means termination without modeled panic or arithmetic failure. A Rust
`Result::Err(PrefixLenError)` is an ordinary successful outer Aeneas result.
Claims about Rust errors must specify their exact branches, not assume success.
Private bit arithmetic lemmas may have additional hypotheses only when public
proofs discharge them from the stated public domain.

All address values and all `u8` constructor inputs are in scope. Receiver methods
requiring a valid network have only the representation invariant `p ≤ w`;
canonical address alignment is forbidden as an additional precondition. Fields
are private in Rust, so invalid-prefix fabricated Lean structures do not describe
safe constructor-produced network states. Raw noncanonical valid states do.

## Initial core obligations

The first intended core is the following family for `Ipv4Net`, `Ipv6Net` and the
corresponding `IpNet` dispatch. If extraction or proof is blocked, mark the
affected APIs unproved; do not replace these obligations with a convenient model.

| API | Required postcondition |
| --- | --- |
| `new(ip,p)` | For every `u8 p`, Rust `Ok n` iff `p ≤ w`, with exact stored `(w,a,p)`; otherwise exactly `Err PrefixLenError`. No input alignment condition. |
| `new_assert(ip,p)` | For `p ≤ w`, exact stored `(w,a,p)` and total success. Invalid prefixes are the documented panic domain and must not be described as verified total success. |
| `addr()` | Exact original stored address, including host bits. |
| `prefix_len()` | Exact stored `p`. |
| `max_prefix_len()` | Exactly `w`, retaining the address family. |
| `netmask()` | Address of numeric value `netmask(w,p)`. |
| `hostmask()` | Address of numeric value `hostmask(w,p)`. |
| `network()` | Address of numeric value `lower(w,a,p)`. |
| `broadcast()` | Address of numeric value `upper(w,a,p)` (also the IPv6 upper endpoint, irrespective of IPv6 protocol terminology). |
| `trunc()` | Exact network `(w,lower(w,a,p),p)`. |

Constructor proofs with exact structure equality are stronger than observer
roundtrips alone and are acceptable. Observer proofs alone do not prove address
arithmetic. A subset of this table is an explicitly partial core, not completion
of the table or crate. Each `IpNet` contract must cover both tags.

Useful derived laws include `lower ≤ a ≤ upper < 2^w`, preservation of `members`
by `trunc`, idempotence of `trunc`, `upper-lower+1=size`, and disjoint network and
host mask bits. These are mathematical helpers unless connected to generated
public bodies. `/0`, `/w`, addresses `0` and `2^w-1`, and arbitrary host bits
must be included by quantified proofs, not only by examples.

## Subsequent coverage obligations

These are the independent extension roadmap, not claims that extraction or
verification includes them. Add exact theorem/API mappings before claiming them.

1. **Mask parsing and construction.** `ipv4_mask_to_prefix` and
   `ipv6_mask_to_prefix` return Rust `Ok p` exactly when the numeric mask equals
   `netmask(w,p)` for a (necessarily unique) `p ≤ w`; all other masks return
   `Err PrefixLenError`. `ip_mask_to_prefix` selects by family. `with_netmask`
   preserves the original address and uses that prefix, and rejects every
   noncontiguous mask. `IpNet::with_netmask` determines the prefix from the mask's
   own family and then validates it against the input address's width; mismatched
   families alone do not cause rejection (for example, an IPv4 address with an
   IPv6 `/24` mask is accepted).
2. **Set operations.** Address containment is exactly membership in `members`;
   network containment is exactly inclusion of the other network's `members`.
   Cross-family containment is false. `supernet` returns `None` iff `p=0`, else
   exactly `(w,lower(w,a,p-1),p-1)`. `is_sibling` means same family, equal positive
   prefix, and equal parent address sets. It does not require distinct children:
   the upstream method also accepts a network as its own sibling. This explicit
   interpretation resolves an ambiguity in the English API name.
3. **Host enumeration.** IPv4 with `p<31` enumerates the inclusive interval
   `[lower+1,upper-1]`; IPv4 `/31` and `/32` enumerate `[lower,upper]`. IPv6
   enumerates `[lower,upper]` for all valid prefixes. Prove ascending order,
   exact contents, no repetition, exhaustion, and termination of each step.
   Do not require collecting `2^128` hosts into a machine-sized vector.
4. **Subnet enumeration.** `subnets(q)` accepts exactly `p ≤ q ≤ w`, otherwise
   returns `Err PrefixLenError`. Its successful iterator enumerates exactly
   `(w,lower(w,a,p)+i*size(w,q),q)` for `0 ≤ i < 2^(q-p)`, in ascending order,
   then is exhausted. Include `q=p`, `q=w`, and `/0` inputs. Public range/subnet
   constructors and iterator methods need their own state-domain contract;
   a proof only for network-produced states must say so.
5. **Aggregation.** For every finite representable input vector of valid networks,
   including empty input, the output consists of canonical valid networks with
   exactly the same union of members, no redundant contained entries, and no
   pair of distinct sibling blocks that could be merged. Establish the promised
   ordering separately. Mixed-family aggregation preserves each family's union.
   Allocation/model assumptions must be recorded, not silently hidden in bounds.
6. **Other APIs.** Parsing, formatting, address arithmetic extension traits,
   conversions, equality/order/hash, defaults, serialization, schema integration,
   and feature-dependent behavior require separately enumerated contracts.
   They are excluded until such contracts and generated-body proofs are present.

## Evidence and trust

Formal scope is fixed by actual extracted bodies, the feature/platform selection,
and audited theorem statements. The Rust-to-Lean extraction and any selected
standard-library models remain trust boundaries and must be identified in results.
Unproved external bodies must not be papered over with application axioms.
Only the allowed foundational Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`) are permitted transitively. Native tests are useful independent
observations, never substitutes for universal contracts.

Specification inputs: the released public API documentation at
[Ipv4Net](https://docs.rs/ipnet/2.12.2/ipnet/struct.Ipv4Net.html),
[Ipv6Net](https://docs.rs/ipnet/2.12.2/ipnet/struct.Ipv6Net.html), and
[IpNet](https://docs.rs/ipnet/2.12.2/ipnet/enum.IpNet.html), plus the captured
release's `upstream/src/ipnet.rs` and `upstream/src/mask.rs` for representation,
domain, and ambiguity checks. The arithmetic model above is independent of the
implementation's bit operations. Release identity is the separate provenance
checker's responsibility.
