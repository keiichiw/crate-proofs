# Expert-guided verification plan

Astra independently defines/reviews contracts; Sol proves actual generated bodies.
The primary reviews trust boundaries, mappings and reproducible evidence. Preserve
all existing total-success contracts and recorded historical runs.

Continuation stopping rule: finish remaining IPv4 work until a new confirmed bug,
a genuinely unresolved blocker, or completion. The previous 243-theorem / 66-
contract evidence is archived in `results-ipv4-core.md`. Start with raw subnet
one-step maximal CIDR choice, exact partition, decreasing Nat remainder and
finite/fixed-prefix enumeration under `ipv4-subnets-specification.md`, then
aggregate and textual parsing/formatting. Existing invalid-q nonempty panic is
already specified; its native reproduction is not a newly discovered bug.

On 2026-10-16 the new heapless feature regression was independently reproduced:
the documented heapless feature fails to select allocation-avoiding serialization,
while legacy ser_as_str does. See bugs/heapless-feature-repro. This met the
user's stopping condition for that continuation. The user then explicitly resumed
remaining verification. The accepted 283-theorem / 66-contract checkpoint is
archived in results-subnet-helpers.md. Resume nonempty next and trace composition;
IPNET-003 is now a known finding, not a new stopping event. Do not claim nonempty
next, complete subnet enumeration or aggregate is proved until audited.

Keep trailing-zero standard-library correspondence explicit. Actual ipnet bodies
must stay extracted. Do not replace sort, merge, parser or iterator algorithms
with desired specifications to make proof completion appear successful.

1. Establish independent Nat CIDR bounds, tagged sets, big-endian octet values and
   endpoint containment laws; classify these as helpers rather than API coverage.
2. Prove actual address/integer and mask/boundary operations against that model,
   using the explicitly recorded Charon/backend compatibility patches.
3. Prove the six concrete Contains cases and corresponding generic public dispatch
   against membership/subset, including all prefixes and noncanonical host bits.
4. Prove raw range transitions, hosts, arbitrary-range/equal-size subnet partition,
   then aggregation exact union preservation. Keep allocation/platform bounds and
   raw constructor error/panic domains explicit.
5. Extend parser/display/serde contracts separately. Record native counterexamples
   for later upstream PRs without modifying the pinned implementation or publishing.

Finite tests and native bug reproductions complement but do not replace proofs.
The theorem inventory, API mappings and most recent accepted full run determine
completed scope; this plan and specifications do not claim implementation coverage.

After containment, use a Nat half-open remaining interval for the first stateful
target, `Ipv4AddrRange::next`, specifying returned value and updated state together.
Keep the Range skip/count branch separate from Subnets→aggregate work: aggregate
does not depend on completing every AddrRange method. Establish exact one-step
partition and decreasing remaining length before full enumeration; prove greedy
maximality separately. Collection allocation and sort/extend model boundaries
remain explicit obligations.

The resumed subnet stage passed full check-rgPh4e3G: 340 audited theorems,
67 public contracts, complete actual IPv4 subnet raw-state classification and
finite/fixed-prefix enumeration. Archived in results-subnet-enumeration.md.
Continue aggregate and parser dependency closure; no new ipnet bug found in
that resumed stage. A temporary parser tool patch is being validated separately.

Continuation stopped at an independently reviewed parser backend blocker:
FnOnce's builtin type loses mutable Parser argument backward state. Reasonable
configuration and narrow tool-fix attempts are recorded in
blockers/ipv4-parser-callback/README.md. Temporary tool changes were archived and
rolled back exactly; no parser proof is claimed. Four reviewed pure aggregate
merge helpers are retained without an aggregate API claim.

The user explicitly resumed by asking to bypass the Aeneas problem and verify
other parts. Defer the known parser/borrowed-callback limitation; do not repeat
that failed path or replace the application parser with a model. Prioritize
extractable actual IPv4 value traits and tagged conversions/dispatch, then any
remaining feasible nonparser APIs. Known dependency blockers on aggregate must
not prevent independent API progress. Baseline check-YVXW5GtO passed 344/67,
archived in results-subnets-parser-blocker.md. No new tool patch is planned.

The no-tool-patch continuation adds independent structural value-trait contracts
for Ipv4Net/Ipv4AddrRange/Ipv4Subnets, tagged V4 hosts/subnets/supernet/sibling
(including unconditional mixed-tag false), and raw preserving conversions.
Full IpNet Default/From<IpAddr> and co-selected IPv6 constructors are included.
Astra reviewed the specifications and actual theorem statements; Sol proved
the actual extracted bodies. Acceptance requires the next frozen full run.
Tagged next, mask dispatch/with_netmask and Hash are deferred after narrow
probes exposed translation/model limitations, documented in extraction-notes.md.
No new tool patch or ipnet source edit is introduced in this continuation.

The user next authorized the proposed order: first the four already-extracted
IpNet V6 hosts/subnets/supernet/is_sibling cases, then IPv6 structural clone/eq/
cmp/partial_cmp for Ipv6Net, Ipv6AddrRange and Ipv6Subnets. Baseline accepted
check-RgsjCQby (369 theorems / 92 public contracts) is archived in
results-tagged-ipv4.md. Astra defines/reviews the independent IPv6 specifications,
Sol proves actual bodies; maintain the existing tool and source pins.

Both ordered IPv6 stages reached checked Lean bodies without a backend change:
concrete4+tagged4 network contracts, followed by 12 raw structural value-trait
contracts. Independent helper proofs cover width128 endpoints/cardinality/parent
relations and actual 16-byte address equality. The final frozen full run must
accept these additions before results.md reports completed coverage.

User resumed toward full IPv6 coverage after check-UBTqNTpY (403/112), archived
in results-ipv6-network-values.md. Inventory every remaining concrete/tagged
IPv6 public surface; prioritize range iteration and subnet next/trace, then
remaining mask/arithmetic/value operations. Independently specify all raw
states, full 2^128 cardinality and usize overflow behavior. Known extraction
limitations must not stop independent extractable APIs; no application model
replacement or claim of whole-family completion from selected bodies.

The current IPv6 continuation has checked/reviewed concrete range nine methods,
finite mixed exhaustion, complete mask conversion/with_netmask, three arithmetic
and four bitwise operations, concrete Default, raw subnet next and actual finite/
fixed-prefix traces. Tagged range nine methods and subnet next compose both
families' concrete contracts. A narrow reviewed standard IPv6 constructor model,
U128 trailing-zero model and exact inherent-selector compatibility fix are
recorded as tool/trust changes. The next frozen full verifier is the acceptance
gate; no selected proof build alone replaces it. Remaining whole-IPv6 obligations
include aggregate, text parsing/formatting, Hash, optional integrations, tagged
mask dispatch, unselected derived/default methods and invalid network domains
not covered by existing valid-prefix contracts. No new ipnet bug was identified.

User resumed remaining work after accepted check-dxnxYoEp (588/142), archived
in results-ipv6-iteration.md. Independent remaining-tagged-specification.md
covers full-family derived values, total runtime new_assert classification,
and mask dispatch including cross-family masks. Resolve generated namespace
shadowing through a reviewed naming correction, never hand editing generated
bodies. Preserve every baseline theorem identity while strengthening constructor
API mappings. Continue narrow aggregate/parser/format/hash boundary diagnosis
where it can yield checked composition; known failures are not proof coverage.
The native IPNET-003 IPv6 extension records the same known heapless cfg defect,
not a new bug or formal serialization verification.

The resumed tagged/value batch has checked actual bodies for cross-family mask
conversion/with_netmask, tagged structural methods and both exported error value
pairs, with new_assert mappings strengthened to full runtime classification.
The additional width-generic minimum-count argument compares the greedy trace
against arbitrary finite canonical exact covers, permitting overlap/duplicates;
its actual-call corollaries require no collection/allocation claim. Acceptance
is gated by the next frozen full run. Direct IPv6 aggregate extraction probes
confirm the unresolved Vec allocation/raw-write relation and are preserved in
blockers/aggregate-extend; parser/Formatter/Hasher/optional-feature boundaries
remain explicit. Native all-features tests pass separately and do not close them.
