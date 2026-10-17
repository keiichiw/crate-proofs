# Extraction investigation (Astra oracle)

These notes record experiments, not verified contracts. Exploratory artifacts are
under ignored `verification/runs/`; the accepted configuration and evidence must
be checked separately. No generated Lean files or Rust implementation were edited
in these experiments, and no application axioms were accepted.

## Concrete address types

Default foreign-body selection leaves `core::net::ip_addr::Ipv4Addr` opaque and
emits a Lean type axiom. This is unacceptable under the verification policy.
Explicit `--include core::net::ip_addr::Ipv4Addr` exposes its real private-field
representation, an array of four bytes. The analogous IPv6 include exposes its
actual representation. Charon's `options.rs` constructs inclusion rules with
`Transparent` opacity, overriding the default `Foreign` opacity. Therefore
`--extract-opaque-bodies` is not necessary for these type definitions.

The independent `oracle-network-a2a0GmQ3` run confirms the concrete IPv4 type
without the global flag. Sol also tested concrete constructor extraction. This
preserves the specification's full address domain, including arbitrary host bits.

The maintained `verification/aeneas.json` subsequently selects 15 public
constructor/observer entries with `extract_opaque_bodies: false` and exactly the
three type includes `core::net::ip_addr::Ipv4Addr`,
`core::net::ip_addr::Ipv6Addr`, and `core::net::ip_addr::IpAddr`.
Its generated address representations are concrete structures and a tagged sum.

## Independent statement review

The final Astra review on 2026-10-16 first rederived the selected contracts from
the vendored upstream public documentation and bodies, before reading the proof
file. It confirmed the constructor/observer specification unchanged. It also
corrected an unrelated extension-roadmap assertion: `IpNet::with_netmask` does
not reject address/mask family mismatch by itself; mask contiguity and whether
the derived prefix fits the address family determine acceptance.

Astra reviewed the 15 theorem statements in `Proofs/Core.lean` against
`specification.md`. The three `new` theorems quantify over all addresses and
all `U8` prefixes, return outer Aeneas success, and specify exact Rust success
or `PrefixLenError` according to the address-family width. `ipNewExpected`
is an independent case distinction on the input family and numeric prefix;
it does not invoke an extracted implementation. Its accepted branches preserve
the exact input address, prefix, and family, and its rejected branches return
the same error. It matches the independent constructor contract.

The three `new_assert` theorems require only the correct width-dependent prefix
bound and preserve exact fields. They make no success claim for invalid prefixes.
The nine observer theorems state exact stored address/prefix or family width.
They are quantified even over invalid-prefix Lean structures, which strengthens
these particular observer statements without imposing an extra Rust API domain
assumption. No theorem adds address-alignment or canonicalization assumptions.

These statements satisfy the corresponding 15 constructor/observer obligations.
This semantic review is separate from compilation, transitive axiom auditing,
source provenance, and extraction correspondence; the runner establishes those
separate checks. It does not approve claims about arithmetic or other APIs.

## Why global opaque-body extraction failed

`scope-explore-NFC7Mjcg/aeneas.log` records 1,525 reachable declarations and
multiple unsupported formatting, panic, and iterator operations, followed by
`Z.Overflow`. The precise overflow is in
`src/symbolic/SymbolicToPureTypes.ml:266`: enum discriminants are converted with
`Z.to_int`. The input LLBC includes `core::mem::alignment::AlignmentEnum` with
`_Align1Shl62 = 4611686018427387904` and
`_Align1Shl63 = 9223372036854775808`, exceeding the OCaml native integer domain.
This is not an overflow in ipnet's network-mask arithmetic. Merely patching this
conversion would leave the unrelated unsupported dependencies unresolved.

Prefer explicit reachable includes, retaining supported Aeneas standard-library
models, instead of globally forcing all dependency bodies transparent.

## Arithmetic investigation and remaining boundary

The smallest tested selection for `Ipv4Net::network` used:

```
--start-from crate::ipnet::Ipv4Net::network
--include core::net::ip_addr
--include core::num::_::max_value
--include core::num::_::checked_shl
--include core::num::_::unchecked_shl
```

The underscores are Charon name-selector wildcards. Explicit `{u32}` selectors
did not match these methods in this pinned Charon. Broad `core::num` inclusion
was worse: it replaced supported byte-conversion model boundaries with actual
`to_ne_bytes`/`from_ne_bytes` bodies that use unsupported transmute operations.

Evidence sequence:

| Run | Observation |
| --- | --- |
| `oracle-narrow-i9Z7h4A5` | `core::net::ip_addr` exposes actual address/integer conversions; `max_value` and `checked_shl` remain opaque because explicit primitive-type selectors did not match. |
| `oracle-num-GIC9rehs` | Broad `core::num` includes trigger unsupported scalar/byte-array transmute and intrinsic axioms. Rejected. |
| `oracle-specific-36fHKuge` | Wildcard method selectors expose `max_value` and `checked_shl`; `unchecked_shl` remains opaque. |
| `oracle-shift-24UQtgdt` | Including `unchecked_shl` leaves `core::ub_checks::check_language_ub` and `core::panicking::panic_nounwind_fmt` opaque. Rejected. |
| `oracle-release-ZSULV8ZX` | Adding Cargo `--release` does not remove those boundaries. Rejected. |
| `oracle-ub-9oCTEBIp` | Including those actual bodies encounters unsupported `ub_checks` and panic evaluation, with further abort/panic implementation axioms. Rejected. |

These runs do not justify a network-arithmetic verification claim. They identify
a concrete extraction boundary for this configuration. The constructor/observer
contracts remain useful independently, but do not establish `network`, masks,
`broadcast`, or `trunc`. Keep the independently stated arithmetic obligations
unchanged and list them as unproved until actual generated bodies pass extraction
and have audited proofs. Do not replace the missing standard-library behavior
with an application axiom, handwritten generated code, or a scalar-only model
while claiming the address-based API was verified.

## Continuation: reviewed runtime compatibility patch

The prior arithmetic blockage above describes the unpatched baseline. During the
expert-guided continuation, `patches/charon-runtime-ub-checks.patch` was applied
to the same pinned Charon revision (no revision upgrade). Astra independently
reviewed the semantics; Sol implemented and rebuilt it. Exact patch text and
binary hashes are enforced by `scripts/check-tools.py` and applied by setup.

The patch lowers only `NullOp::UbChecks` when the crate's recorded `ub_checks`
setting is **true**, to boolean true. Pinned Charon's AST documents that runtime
value and its MiniRust backend already follows it. True also agrees with that
intrinsic's const-evaluation value; when runtime UB checks are false, this patch
leaves the operation untouched instead of unsoundly substituting false in const
contexts. Other nullary operations are unchanged. The false-setting probe
`sol-patch-false-QvQYBszG` retains the unsupported operation and is rejected.

The patch additionally recognizes `core::panicking::panic_nounwind_fmt` as an
unconditionally diverging panic helper in Charon's existing panic reconstruction.
This supports total-success/no-failure contracts, not preservation of unwinding
versus abort observables. No application model, generated Lean rewrite, or custom
axiom is introduced. The translator and this reviewed compatibility patch remain
part of the explicit trust boundary; a source review is not a metatheoretic proof
of Charon correctness.

Important configuration nuance: pinned Charon defaults to a Miri sysroot
(`charon/src/bin/charon/main.rs`, `setup_miri_sysroot`). In its extracted core,
`check_language_ub.runtime` is `!cfg!(miri)`, hence false. The optional Rust
language-UB diagnostic branch is skipped even when `runtime_checks.ub_checks`
is true. This is not caused by substituting false in the patch. Shift safety must
therefore be established from `checked_shl`'s `rhs < BITS` branch and Aeneas scalar
operation requirements, not inferred from diagnostic checks executing. The full
verifier explicitly checks the LLBC settings: UB and overflow checks true,
contract checks false. Claims concern runtime method behavior, not general
compile-time const-evaluation semantics.

`sol-patch-net-V0ql12Oh` successfully extracts concrete IPv4 network arithmetic
without axioms. `sol-allarith-K69iFPjN` extends this to `netmask`, `hostmask`,
`network`, `broadcast`, `trunc` for both widths and IpNet dispatch. Extraction
success alone does not establish these contracts: the maintained theorem ledger
and accepted full run determine which have been proved.

## Contains-specific boundaries found during continuation

The shared extractor now accepts narrowly validated local trait selectors via
`impl_entries`, e.g. `{impl crate::ipnet::Contains for _}::contains`. This selects
all six concrete Contains implementations, unlike selecting only the generic
public dispatch method. The generic public specialization must still be proved
with the actual trait dictionary to claim its full API behavior.

Additional probes reach address-comparison dependencies: IPv4 array/slice
comparison and IPv6 `segments()` transmute from 16 bytes to 8 u16 values. Broad
standard-library inclusion also encounters a u8 comparison type mismatch.
These are distinct from the resolved checked-shift blocker. No axiom-bearing
Contains extraction is accepted and none of these findings alone establishes a
Contains theorem. Probe outputs remain in ignored run directories.

### Checked shift names in the Lean backend

The axiom-free expanded extraction initially failed to compile because emitted
`U32.shl`, `U32.shr`, `U128.shl`, `U128.shr` intrinsic names were absent from the
pinned Lean library. `patches/aeneas-checked-intrinsic-shifts.patch` adds exactly
four wrappers delegating to the existing `UScalar.shiftLeft_UScalar` and
`UScalar.shiftRight_UScalar`. Each requires the count to be less than the value's
bit width; otherwise the existing Result model fails with integer overflow.
No arithmetic meaning, axiom, or unchecked shift behavior was substituted.
Astra reviewed this addition and its total-success interpretation. The same patch
is enforced on both the dedicated Aeneas checkout and actual Lake dependency.
The shift-only stage did not change the OCaml extractor executable; the later
unwrap registration change below rebuilds it. Public proofs must discharge these
shift bounds even though the Miri library's optional diagnostic branch is false.

### Unused Debug dictionary in Result::unwrap

The first expanded axiom audit rejected the three `trunc` contracts: the
generated call to `Result::unwrap` carried a `Debug<PrefixLenError>` dictionary,
whose type transitively referenced the standard backend's opaque `Formatter`
axiom. Valid-prefix `trunc` returns `Ok` before this call; no formatting executes.
Nevertheless, build success did not meet the transitive axiom audit requirement.

Astra rejected replacing the entire Formatter model with Unit. The reviewed
alternative uses Aeneas's supported `keepTraitClauses` metadata to erase only
the unused Debug argument from the unwrap model. The original unwrap model
ignores that dictionary in both its Ok and Err branches; an exact equality
check establishes that the dictionary-free wrapper has the same Result behavior.
The original Formatter and formatting models remain unchanged. This is a
backend model registration change, not an edit to generated ipnet Lean.
Enabling this supported metadata exposed a one-line OCaml validation defect:
the trait-filter length was compared with the number of type parameters rather
than trait clauses. The combined patch compares it with the actual clause count;
the filter operation and type-parameter validation remain unchanged.
The combined patch is `patches/aeneas-runtime-model-compat.patch`, retaining
the four checked shift wrappers above. The accepted theorem inventory and full
run, rather than this diagnosis, determine whether `trunc` is verified.

## Containment continuation: minimal IPv4 comparison diagnosis

The second expert response (`expert-contains-review.txt`) prioritizes actual
comparison-path connection before introducing a replacement comparison model.
The broad include probe `sol-v4-full-0YnjUDcT/ipnet.llbc` explains the previously
reported type mismatch: function declaration 59 is the pinned core `u8` Ord cmp
(`core/src/cmp.rs:2347`), whose statement 519 assigns `BinaryOp Cmp` to an
`Ordering` enum destination. Pinned Aeneas `InterpExpressions.ml:1168` instead
constructs a signed i8 result for that operator; the interpreter rejects the
destination type. This does not show a defect in ipnet containment.

The narrower reference-Ord include in `sol-v4-exact-gjshYM30` avoids extracting
the scalar cmp body and retains the existing Aeneas `core.cmp.OrdU8` model.
Its generated IPv4 path is actual ipnet Contains (`ipnet.rs:1450/1456`) →
`Array.Insts.CoreCmpOrd.cmp` → array full-range index to slice →
`Shared0A.Insts.CoreCmpOrd.cmp` → `SliceOrd.Blanket.compare` →
`chaining_impl` and its loop. This probe connects the relevant comparison body
without broad slice/raw-pointer extraction. It still has unused PartialOrd
dictionary-field dependencies and a ControlFlow branch dependency, so probe
translation alone is not accepted evidence. `sol-v4-exact-6YZldKLI` additionally
extracts the exact ControlFlow branch. The final maintained configuration,
model-correspondence ledger and accepted audit determine completed coverage.

### Selected concrete comparator boundary

Closing the remaining unused Slice PartialOrd dictionary fields in
`sol-v4-closure-djQhu1U6` reaches generic `as_underlying` and pointer/lifetime
dependencies unrelated to containment. Following the expert's fallback order,
the selected route registers concrete IPv4/IPv6 octet structures and only their
`Ord::cmp` methods in the version-local Aeneas backend `Std/NetIpAddr.lean`.
The modeled methods compare existing U32/U128 big-endian byte interpretations.
Their Rust correspondence is reviewed trusted, not proved by the Lean kernel.
In particular, the IPv6 model includes the segments/transmute/array-comparison
chain within this reviewed boundary; no separate implementation proof of
`segments()` or general transmute support is claimed.

The shared extractor supports `charon_opaque` for concrete standard-library
selectors, rejecting local application selectors, wildcards, and combination
with `extract_opaque_bodies`. This enables choosing the two registered comparators
without dragging their unused dependency dictionaries into extraction. All
generated-axiom/incomplete-output checks remain enforced. The actual ipnet
Contains bodies, public generic wrappers and partial_cmp are still extracted.
Default le is connected through the existing Aeneas Std/Core/Cmp model, which
returns true exactly for partial_cmp results Some Less or Some Equal; its Rust
correspondence remains a standard-library model boundary. Probe `sol-v4-model-iwlOKRrc` validates the IPv4 route; the shared
extraction `sol-contains-extract-4S2gJlml` includes both families and public
wrappers without generated axioms or errors. Neither probe alone is a proof.
See `model-boundaries.md` for the exact correspondence classification, reviewed
source and preserved input domains. Final inventory and full evidence determine
the accepted implementation contracts under those explicit boundaries.


## IPv4 range `next` continuation

The minimal probe `sol-range-probe-fXsQFNiL` established that selecting
`{impl core::iter::traits::iterator::Iterator for crate::ipext::Ipv4AddrRange}::next`
extracts the actual mutable method with result type
`Result ((Option Ipv4Addr) × Ipv4AddrRange)`. The broader existing configuration
plus this exact selection (`sol-range-full-z436i5yo`) resolves its dependencies
without generated axioms: the actual IPv4 constructor, IpStep replacements and
increment, IpAdd saturating addition, and next body are emitted. The existing
reviewed IPv4 comparison boundary is reused.

The shared extractor's `foreign_impl_entries` accepts only a named standard
trait, a concrete local `crate::` type, and a named method. Foreign receiver
models, wildcard receiver/trait/method and argument injection are rejected;
generated axiom/incomplete-body checks remain enforced. This is an entry-point
selection mechanism, not permission to replace the iterator implementation.
Proof acceptance still requires the combined returned-value/updated-state
contract and the final full verifier.

The range continuation also adds `core.num.U32.saturating_add_val` inside the
existing backend scalar module: a kernel-checked exact-min lemma about its
unchanged saturating-add definition. It neither replaces that definition nor
adds a Rust semantic model. The combined pinned backend patch includes this
lemma; the range proof audits its transitive dependencies. Cross-module unfolding
of the wrapper was unavailable with the module's existing visibility, so the
lemma is proved in its defining module instead of changing the model's semantics.


## IPv4 API breadth continuation

The range probe `sol-range-max-knogdi5a` extracts all eight remaining custom
Ipv4AddrRange methods. Including the exact `core::legacy_int_modules::usize::MAX`
resolves the only constant axiom using the existing Usize MAX definition.
The shared required-definition matcher now permits whitespace/newlines after
`def`, as the generator emits multiline names for some DoubleEndedIterator
methods. Required exact escaped names and unsupported-body rejection are retained.

The network probe `sol-netops-probe-6flzz3z6` exposed Result map/ok dependencies.
Broad `core::result` inclusion (`sol-netops-result-62mhsc_v`) failed extraction;
narrow `core::result::_::map` and `::_::ok` (`sol-netops-narrow-q81ou5bu`) produced
a valid actual map body but failed on ok with `There should be no bottoms in the
value`. Its partial output is rejected and not maintained. Following independent
Astra review, only ok uses an exact match model returning Some for Ok and None
for Err. Its reviewed Rust correspondence is restricted to the selected drop-free
Ipv4Net/PrefixLenError application; generic effectful destructors are not proved.
The actual map body remains extracted. core/src/result.rs is source-hash pinned.

Shared extraction `sol-batch-shared-generated` integrates the range methods and
network hosts, supernet, is_sibling, subnets initialization, Default and From.
The maintained model is regenerated, with no generated axiom/sorry. Formal
coverage still requires completed contracts and the accepted full verifier;
extraction success is not a verification claim. Saturating subtraction uses a
kernel value lemma about the existing unchanged U32 scalar model.

The optional IPv4 mask probe resolves leading_ones by narrowly extracting its
actual Rust body (`!self` followed by the existing leading_zeros model), using
`core::num::_::leading_ones`. No additional semantic model is needed for this
path. Mask construction must still prove success iff the independent contiguous
mask formula, including invalid masks, before receiving public coverage.

For IPv4 bitwise overloads, concrete local-trait / standard-address receiver
selectors avoid selecting the unrelated IPv6 overloads. The shared impl_entries
validator accepts a concrete standard receiver path as well as its existing
local-trait wildcard form; no arbitrary command fragments or opaque local body
selection are enabled. Regression checks retain generated-axiom rejection.

## IPv4 subnet iteration initial extraction checkpoint

The narrow `sol-subnets-probe` selected `next_ipv4_subnet` and the concrete
`Iterator for Ipv4Subnets::next` body. Its generated model was rejected because
`U32::trailing_zeros` and `trailing_ones` remained axioms. The accepted
`sol-subnets-probe2` instead uses one reviewed fixed-width `U32::trailing_zeros`
model: reverse its 32-bit vector and count leading zeros. Aeneas represents it
as an ordinary `Result.ok` call. The source body of `trailing_ones` is narrowly
extracted with `core::num::_::trailing_ones`; it complements the value and calls
the modeled `trailing_zeros`. This preserves the complete actual helper and
iterator bodies without a generated axiom or an application-body replacement.
The fixed-width intrinsic correspondence is a reviewed standard-library model
boundary. The generated model compiles, and exact input hashes are checked by
the full verifier; no nonempty iterator API contract is claimed at this checkpoint.

The independent subnet mathematics and bitcount threshold lemmas are audited
helpers. An actual-body theorem proves already-empty raw states return `None`
and preserve their state for every stored U8 prefix. The nonempty greedy block,
post-state, invalid-prefix panic classification, finite trace, and composition
with `Ipv4Net::subnets` remain unproved. A raw nonempty iterator with minimum
prefix above 32 reaches `Ipv4Net::new(...).unwrap()` and panics; the domain is
explicit in `ipv4-subnets-specification.md` and is not a normal-success claim.

Separate `sol-aggregate-probe` selected `Ipv4Net::aggregate` and exposed its
actual loop bodies, but the shared extractor rejected unresolved generated
standard-library axioms, including iterator mapping, slice sorting and
`last_mut`, tuple ordering, and vector extension. It was not copied into the
maintained model. Those boundaries require narrow models or actual extraction
and composition before any aggregate API claim.

The initial subnet limitations above were subsequently discharged in
check-rgPh4e3G (340 theorems / 67 contracts), including actual nonempty next,
invalid-prefix classification and complete finite/fixed-prefix enumeration.
The aggregate boundary remains unresolved. See results.md for current evidence.

## Tagged and derived value-trait selection

Official isolated probes under `verification/runs/sol-tagged-{basic,hosts,sibling,subnets,supernet}` and
`verification/runs/sol-derived-{clone,eq,cmp,partialcmp,ipv4addrrange,ipv4subnets}`
extracted actual bodies without an Aeneas patch. The combined clean selection
under `sol-tagged-derived12` adds exact `From` constructors for both address-range
and subnet-iterator tags, the selected `IpNet` hosts/supernet/is_sibling/subnets
bodies, and Clone/PartialEq/Ord/PartialOrd bodies for `Ipv4Net`,
`Ipv4AddrRange`, and `Ipv4Subnets`. The generated Lean builds with the previous
proof modules. The tagged V4 specialization and structural trait contracts are
audited separately; extraction alone is not a proof of their behavior.

The `sol-tagged-{subnetsnext,rangenext}` probes both reach the pinned
`Ipv6Addr::new` body and fail Aeneas on
`transmute<[u16; 8usize], [u8; 16usize]>`; neither tagged iterator `next`
body is maintained. The `sol-tagged-combined` probe generated
`mask.ip_mask_to_prefix (mask : IpAddr)` with branch calls
`mask.ipv4_mask_to_prefix` and `mask.ipv6_mask_to_prefix`. Lean resolves
`mask` as the parameter, so both projections fail. `IpNet::with_netmask` depends
on that function, and both were omitted from the clean no-tool-patch batch.
The `sol-derived-hash` probe generated unmodeled `U8`/`U32` hash axioms and
was rejected by the extractor's incomplete-model filter. None of these
rejected outputs were copied into the maintained Lean model.

## IPv6 tagged branches and derived value traits

The previously selected `IpNet::{hosts,subnets,supernet,is_sibling}` bodies
already contained their V6 branches. The checked `IPv6NetOps` contracts now
connect those calls to 128-bit network, broadcast, truncation, and containment
proofs, and `TaggedIPv6` proves the four actual tagged V6 dispatch branches.
No generated source or extractor model was changed for these eight contracts.
The independent `IPv6NetMath` establishes the full /0 interval of length
`2^128`, the /128 singleton, and same-parent arithmetic; it is helper evidence,
not IPv6 iterator enumeration.

The official `verification/runs/sol-ipv6-derived12` probe selected the actual
Clone, PartialEq::eq, Ord::cmp, and PartialOrd::partial_cmp bodies for
`Ipv6Net`, `Ipv6AddrRange`, and `Ipv6Subnets`, with no Aeneas patch or new
trusted model. The maintained generated Lean is copied exactly from that
successful extraction. `IPv6AddressEq` connects the selected concrete IPv6
array equality body to the independent 16-octet big-endian value; the derived
proofs compare raw stored fields, not CIDR-set or remaining-iterator equality.
They do not imply IPv6 iterator `next` or aggregate coverage.

The IPv6 standard constructor requires Charon's exact inherent selector
`core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::new` for opacity; the shorter
path did not select the inherent body. The shared extractor validator now accepts
that concrete standard-library inherent form, in addition to existing exact trait
forms. It still rejects local application receivers/wrappers, wildcards and
injected arguments/newlines, and still rejects generated axioms. The changed
helper suite passes 16 tests. This selection makes the reviewed standard model
available; it does not hide any ipnet implementation body.

Further investigation corrected the initial interpretation of the constructor
probe: the pinned Charon matcher returned false unconditionally for inherent
`ImplElem::Ty` patterns. Default standard-library opacity made the standalone
probe succeed; it did not demonstrate an exact-selector match. With broad
address inclusion enabled, that inclusion was the only matching rule. This is
not an include/opaque priority inversion. The continuation reviews a minimal
matcher completion delegating the concrete implementation type to the existing
`NamePattern.matches_ty`. Its exact source/binary patch and fresh extraction
must be checked before accepting the resulting constructor selection.

## Tagged iterator continuation after the constructor boundary

Official fresh probes `verification/runs/sol-tagged-range/` select the nine
IpAddrRange Iterator/DoubleEndedIterator overrides; `sol-tagged-subnets-2/`
adds actual IpSubnets::next. Maintained Ipnet.lean is copied from the latter
successful extraction. The previously recorded constructor/transmute obstacle
for these methods is resolved by the reviewed narrow standard constructor
boundary and exact selector fix above; the application forwarding bodies remain
actual extracted Rust. Both family branches are required in the new independent
contracts. No additional semantic model is introduced by tagged dispatch.
The historical mask-name-shadow and Hash probes remain separate unresolved
limitations. Successful extraction alone is not the acceptance criterion;
public contracts require the frozen full-run audit.

## Resumed tagged mask name hygiene

After baseline check-dxnxYoEp, the generated mask namespace shadowing is
addressed in Aeneas ExtractBase.basename_to_unique: for Lean, an existing
ordinary dotted declaration beginning with candidate plus dot counts as a local
name collision. The existing allocator then alpha-renames the binder and all
references through its name map. The official narrow probe builds and changes
only three mask-function binder spellings; no Rust/application body is replaced.
Astra and primary reviewed the exact patch. It scans the ordinary names_set;
it is not a proof of universal hygiene for every strict-name or backend case.
Final maintained extraction/patch/binary pins and full verification remain
required before accepting the new mask API contracts.

The successful maintained continuation then selects twelve tagged derived
methods (`sol-tagged-derived-extract`) and the exported singleton error value
methods (`sol-prefix-error-derived`, `sol-addrparse-error-derived`). Maintained
Ipnet.lean is the untouched output of the last successful extraction. The
AddrParseError selection concerns only Clone/eq, not parser algorithms. Unit
clone required the visibility-only existing-model lemma recorded in the ledger.

The narrow aggregate extension probes now have a persistent record at
blockers/aggregate-extend/README.md with exact configurations, rejected generated
text and evidence hashes. The final probe directly selects Ipv6Net::aggregate;
the same Vec::extend_desugared allocation/raw-pointer-write boundary is observed
for both families. These rejected models are never imported into maintained
proofs. The precise probe Aeneas patch is saved beside the evidence, predating
the later Unit clone visibility lemma.

The name-hygiene/Unit changes do not repair generic Formatter/Hasher effects
or the parser's mutable FnOnce backward-state mismatch. The earlier rejected
sol-derived-hash output contains unresolved U8::hash, U32::hash and
U32::from_ne_bytes dependencies. No new hasher or formatter model is admitted,
and no inherited/default consumer correctness is inferred from value proofs.
