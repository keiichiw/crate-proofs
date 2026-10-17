# IPv6 continuation coverage

Acceptance is determined by results.md and the frozen verifier output, not this
plan or extraction alone. The network/value baseline check-UBTqNTpY has 403 theorems / 112 public
contracts. The network/value stage uses ipv6-tagged-value-specification.md; range, numeric
and subnet continuation uses ipv6-iteration-specification.md.

## Network initialization and relations

The expansion proves Ipv6Net hosts, subnets, supernet and is_sibling, and their
IpNet V6 specializations. All use valid stored network prefix ≤128 and arbitrary
host bits. hosts returns exact full block endpoints at every prefix; /0 has
mathematical cardinality 2^128 and /128 has one address. subnets covers every
requested U8 prefix, including ordinary error cases. supernet handles /0 None
and canonical immediate parents; sibling is positive equal prefix plus same
parent, including self. These are initialization/relation contracts, not
IPv6 address/subnet iteration or collection success.

## Structural value traits

The expansion proves actual clone/eq/cmp/partial_cmp for Ipv6Net,
Ipv6AddrRange and Ipv6Subnets. The domain is every raw state, including prefix
values >128 and reversed endpoints. Keys are stored fields in declaration
order, with network-order numeric addresses. Structural equality does not
identify distinct representations of one set. Hash, formatting, inherited
trait defaults and marker traits receive no implicit algorithm coverage.

## Existing and excluded scope

Previously accepted IPv6 constructor/observer, mask/network/broadcast/trunc,
containment and simple conversion contracts remain in the theorem inventory.
The concrete IPv6 comparator correspondence remains a reviewed trusted model;
its full Rust implementation is not independently proved.

The accepted baseline did not cover Ipv6AddrRange iterator methods or
Ipv6Subnets::next/enumeration; their continuation status is recorded below.
Aggregate, textual parser/formatter, Hash, optional serialization/schema
integrations and inherited consumers remain outside the completed scope.
The Ipv6Addr::new transmute extraction boundary is now handled by a narrowly
reviewed standard constructor model and concrete inherent-selector matcher fix.
Actual ipnet iterator bodies remain extracted. Acceptance of dependent proofs
requires the full-run result; no application iterator model is substituted.

## Range, numeric and subnet continuation (acceptance gated by results.md)

Actual Ipv6AddrRange next/next_back/nth/nth_back/count/size_hint/last/min/max
contracts now have checked Lean bodies. Every raw endpoint pair is included.
The usize-sensitive methods use an explicit pinned64 premise. count normally
returns exact Nat cardinality when it fits usize and otherwise fails with
integerOverflow under checked extraction; this is not a saturating count or
a release-profile wrapping guarantee. nth/back and size_hint succeed even for
the full 2^128-cardinality range without computing that count in U128.

Ipv6Net Default, ipv6_mask_to_prefix/with_netmask and all three arithmetic/four
bitwise overloads have checked actual-body contracts. Mask conversion is a
complete iff, including noncontiguous rejection, zero and all-ones; with_netmask
preserves original host bits. Arithmetic saturates and bitwise operations use
independent network-order numeric values. Public API acceptance remains tied
to the next full verifier, not extraction or the proof module build alone.

The actual Ipv6Subnets next and unconditional actual finite/fixed-prefix trace
contracts now have checked Lean bodies. They cover reversed ranges for every
stored q (normal None), live q<=128 (largest aligned eligible CIDR and exact
residual), and live q>128 (modeled panic). Trace existence and exact partition,
order, disjointness and canonical blocks compose actual next equations; the
LiveLaw parameter of intermediate lemmas is discharged in final theorems.
Fixed-origin enumeration has mathematical length 2^(q-p), with no allocation
success claim. Final acceptance still requires the frozen full verifier.

Full-family IpAddrRange forwarding (nine overrides) and IpSubnets::next have
checked actual-body proofs reviewed against independent contracts. Both families
retain exact concrete output tags and raw updated states; range observations
compose independent half-open interval contracts. Count includes the explicit
checked-overflow branch, and subnet dispatch includes invalid-live panic. Tagged with_netmask
and ip_mask_to_prefix retain the recorded generated namespace-shadow blocker;
concrete IPv6 mask methods are covered by the staged numeric proofs. Aggregate,
parser, formatter, Hash and optional features retain their separate boundaries.
These exclusions prevent a claim of whole-IPv6 or whole-crate completion.

## Exact scope qualifications

Network operation contracts retain their stated valid stored-prefix domains;
new_assert currently has a valid-prefix success contract, not an invalid-prefix
panic contract. Raw invalid network values are not silently covered by these
valid-input results. Structural trait contracts and raw iterator contracts
separately state their broader domains. Tagged enum derived traits, inherited
comparison defaults and iterator consumers are not inferred from concrete
family implementations or from marker traits.

## Resumed remaining obligations after check-dxnxYoEp

The accepted range/numeric/subnet/tagged-iterator batch is recorded in results.md
and archived results-ipv6-iteration.md (588/142). Subsequent work uses
remaining-tagged-specification.md: tagged structural traits for all raw states,
full runtime new_assert success/assertionFailure classification, and tagged
mask dispatch including mixed-family masks. The generated namespace-shadow
obstacle now has a reviewed binder alpha-renaming correction; final acceptance
still requires actual contracts and the frozen full verifier.

A further mathematical/actual-trace obligation compares subnet enumeration
length against arbitrary finite canonical CIDR covers of the exact same range,
with the same minimum prefix. Competitor covers may overlap or repeat blocks.
This global minimum-count law is not inferred merely from one-step greediness
and now has checked pure and actual-call corollaries reviewed by Astra; full-run acceptance remains gated by results.md. It adds a semantic law, not a
new public method count. Aggregate, parser, formatting, Hash and optional-feature
implementation proofs remain separate.


The resumed batch now has checked/reviewed actual contracts for tagged mask
and with_netmask dispatch, all twelve tagged structural value methods, full
runtime new_assert classification and four singleton error Clone/eq methods.
Old valid-only constructor theorem identities are retained as helpers; their
three API mappings now refer to full-domain contracts. NewAssert failure is
assertionFailure in the extracted model (Rust assertion panic); this does not
claim const evaluation, messages or unwind/abort equivalence.

SubnetMinimumMath and SubnetMinimumActual prove minimum output count for both
widths against arbitrary finite canonical exact-cover lists with p>=q. The
competitors can be unordered, overlapping and duplicated. Final corollaries
use the already checked actual finite traces, including terminal None, with
mathematical Nat lengths and no allocation promise. These are helper/semantic
laws, not additional public methods. The resumed whole-run candidate is
625 theorem identities /160 public contracts; only results.md determines its
accepted status. Parser, aggregate, Formatter/Hasher effects and optional-feature
proofs remain outside this batch, with direct aggregate evidence preserved at
blockers/aggregate-extend/README.md.
