# Model correspondence ledger requirements

Astra independent acceptance criteria, 2026-10-16. This document defines the
required ledger format for the containment extension; it does not preapprove
any new model. The integration owner must populate concrete rows after selecting
the extraction paths. Existing baseline standard-library and extraction trust
still applies and must remain identified in results.

Every new or changed model boundary requires one row with these fields:

| Field | Required content |
| --- | --- |
| Rust operation | Exact fully qualified symbol and concrete type/trait instantiation |
| Source/configuration | Pinned source revision/location, target/endian, features and relevant cfg |
| Lean operation | Exact model definition, registration and any adapter |
| Contract | Full input domain, total-success/error behavior, output and state observations |
| Correspondence class | One of the three classes below |
| Evidence | Exact theorem names or source review and its rationale |
| Unproved boundary | What is assumed rather than kernel-proved |
| Consumers | Actual public theorems whose guarantees depend on this row |
| Reproduction | Patch/hash and regeneration/build/audit commands or evidence paths |

The correspondence classes are:

1. **Proved against extracted body.** State the exact equality/refinement theorem
   between the helper and the actual generated operation; audit its dependencies.
2. **Proved against established primitive semantics.** Identify that semantics,
   the concrete operation and correspondence theorem. Do not describe the
   Rust-to-primitive translation itself as proved unless it actually is.
3. **Reviewed trusted Rust/model correspondence.** Identify the concrete pinned
   Rust operation and exactly why its hand-written model matches. State explicitly
   that this correspondence is not proved in Lean. Kernel proofs about that model
   remain model proofs. Public results must say they are conditional on this
   reviewed standard-library correspondence.

For an adapter-only repair, prove or inspect preservation of compared slice
length/elements/order and retain the original comparison model's trust status.
For comparison models, record full Ordering and all input digit patterns; for
segments, record whether the boundary is the full method or raw native-endian
transmute. A full-method BE model must not retain a subsequent from_be swap.
No general Formatter, arbitrary transmute, or arbitrary comparator model may be
inferred from a concrete trusted row. No unproved assumptions may be hidden in
terms such as "axiom-free" or "verified comparison".

## Selected containment boundaries

Astra reviewed the following source/model choices on 2026-10-16. The user
explicitly permits small reviewed standard-library models. The four new boundary rows below
are **reviewed trusted Rust/model correspondence**, not Lean proofs of that
correspondence. The model definitions have no new Lean axioms; that fact does
not strengthen the correspondence classification.

| Rust operation | Selected Lean representation/model | Review basis and unproved correspondence |
| --- | --- | --- |
| `core::net::ip_addr::Ipv4Addr` | `NetIpAddr.lean`: structure with `octets : Array U8 4#usize` | Pinned `ip_addr.rs:74` has precisely `[u8;4]`. Same field and full octet domain as prior generated type. Replacement of generated type registration by hand-written concrete type is a new reviewed representation boundary; Rust layout correspondence is not proved. |
| `core::net::ip_addr::Ipv6Addr` | `NetIpAddr.lean`: structure with `octets : Array U8 16#usize` | Pinned `ip_addr.rs:168` has precisely `[u8;16]`. Same field and full domain as prior generated type. Representation/layout correspondence is reviewed, not proved. |
| `Ord::cmp` for `Ipv4Addr` | `ipnet.core.net.ip_addr.Ipv4Addr.Insts.CoreCmpOrd.cmp`: normal success with Nat comparison of `U32.from_be_bytes` values | Pinned `ip_addr.rs:1296` compares four octets; `array/mod.rs:453` delegates to same-order slices, whose comparison is lexicographic (`slice/cmp.rs`, including byte specialization). Equal length and digits below 256 imply this numeric ordering. The complete Rust comparison/array/slice/model link is trusted by review; no extraction proof of that link is claimed. |
| `Ord::cmp` for `Ipv6Addr` | `ipnet.core.net.ip_addr.Ipv6Addr.Insts.CoreCmpOrd.cmp`: normal success with Nat comparison of `U128.from_be_bytes` values | Pinned `ip_addr.rs:2302` compares eight segments. `segments` at 1525 transmutes native-endian U16 words then applies `from_be`; on the checked little-endian target each pair is swapped once, producing `256*b[2i]+b[2i+1]`. Eight bounded base-65536 digits compare like the original 16 big-endian octets. This entire concrete comparator bridge is reviewed trusted, including segments and array/slice comparisons; segments implementation is not independently proved. |

The selected Lean source is
`.tools/aeneas/backends/lean/Aeneas/Std/NetIpAddr.lean`; its `rust_type` and
`rust_fun` registrations are regenerated into `ExtractBuiltinLean.ml`.
The registered concrete type names are `ipnet.core.net.ip_addr.Ipv4Addr` and
`ipnet.core.net.ip_addr.Ipv6Addr`, preserving the former generated fully qualified
names. Only the two concrete `Ord::cmp` functions are selected as opaque modeled
operations. Actual generated `partial_cmp` and ipnet `contains` bodies remain the proof
targets. Default `le` uses the existing Aeneas model in `Std/Core/Cmp.lean`
(`Aeneas.Std.core.cmp.PartialOrd.le_body`, `le.default`, and registered
`le.trait_default`), not a separately extracted Rust body. This baseline trusted
model returns true exactly for `Some Less` or `Some Equal`, matching the pinned
Rust `PartialOrd::le` default at `cmp.rs:1520`, which calls
`self.partial_cmp(other).is_some_and(Ordering::is_le)`; `Ordering::is_le` accepts
Less and Equal.
Its correspondence is reviewed, not newly kernel-proved against Rust. Their equalities to Nat decisions are kernel
proofs conditional on these comparator/type correspondences and the existing
standard-library byte conversion models. No generic comparator or transmute
model is introduced. No additional from_be is applied after the numeric model.

The IPv4 isolated extraction probe is
`verification/runs/sol-v4-model-iwlOKRrc`: reviewed generated output retains
`partial_cmp → Ord::cmp`, default `le`, and actual address/network `Contains`
bodies. Its lack of generated axioms/errors is extraction evidence, not completed
containment proof evidence. Integration must record the final regenerated model,
theorem inventory/audit, patch hashes, and full verifier result for both families.

`toolchain.json` records extraction Rust commit
`923c95cdf5ba65cea505aa2ea829f578e1506ed8`, target `aarch64-apple-darwin`,
little endian and 64-bit pointers. `std-source-boundaries.json` pins hashes of
`net/ip_addr.rs`, `array/mod.rs`, `slice/cmp.rs`, `cmp.rs`, and `uint_macros.rs`;
`check-tools.py` verifies source/config identity. Those checks preserve the
reviewed inputs and do not prove Rust/model correspondence.

Existing constructor/observer/arithmetic contracts use the same fixed-length
`octets` field and the same independent weighted-byte interpretation. The new
registered type does not narrow their domains or alter their mathematical
postconditions. Rebuilding and auditing all existing contracts is still required;
their reported trust boundary now includes the reviewed concrete type registration.
The implemented comparison bridge is `Comparisons.ipv4_cmp_spec` /
`ipv6_cmp_spec`, with exact full Ordering; `ipv4_partial_cmp_spec` /
`ipv6_partial_cmp_spec` connect the extracted methods to `Some` of that Ordering;
`ipv4_le_spec` / `ipv6_le_spec` connect the existing default-`le` model to numeric `≤`. These
statements were independently reviewed for arbitrary octet inputs, without
additional alignment or value assumptions. `array_to_slice_val` preserves the
entire sequence but is a helper, not evidence that the trusted comparator body
was extracted. Final comparison/containment theorem names and evidence paths must be taken
from the final inventory rather than inferred from this review.

This ledger is distinct from `theorems.json`: the theorem audit checks permitted
Lean axioms and dependency closure; the ledger records semantic trust at Rust
boundaries that can exist even when every Lean definition is axiom-free.

## Final containment statement and instance review

Astra independently reviewed `Proofs/Contains.lean`: the six
`ipv4_contains_addr_spec`, `ipv4_contains_net_spec`, `ipv6_contains_addr_spec`,
`ipv6_contains_net_spec`, `ip_contains_addr_spec`, and `ip_contains_net_spec`
statements, and their six `*_public_contains_*_spec` counterparts, require normal
success and equivalence to independent membership/subset. Prefix validity is the
only network assumption; arbitrary host bits and endpoint prefixes remain in
scope. The tagged cases cover both same-family and both mismatched-family cases.
`CidrModel.subset` means operand-set inclusion in receiver-set, and the checked
endpoint equivalence connects it to the implementation's comparisons.

The two `IpNet` public specializations use the named `selectedIpContainsAddr`
and `selectedIpContainsNet` definitions, each assembling a typed
`ipnet.ipnet.Contains` record whose sole `contains` field is the corresponding
actual extracted `IpNet.Insts.…contains` method. Aeneas emitted those methods
but not standalone unused dictionary records. This assembly is exact dictionary
elaboration: the generated trait has one field and no supertraits, associated
items or additional laws; pinned Rust `upstream/src/ipnet.rs:1429` and `:1439`
identify those implementation methods; the extracted public wrapper simply
projects and calls that field. It introduces no replacement algorithm or
additional standard-library semantic model. It is recorded here to make the
selected public trait specializations explicit.
In the final integration LLBC (`sol-contains-extract-4S2gJlml`), the Contains
trait is id 6, the IpNet-operand implementation is trait-impl id 6 / method 48,
and the IpAddr-operand implementation is trait-impl id 7 / method 49. The named
proof-side dictionaries are `ipnet.selectedIpContainsNet` and
`ipnet.selectedIpContainsAddr`. These numeric IDs identify this extraction only;
the Rust symbols and exact generated method names are the semantic identities.

This semantic review does not substitute for the final clean regeneration,
whole-package build, transitive axiom audit or before/after fingerprint checks.
The final verifier result and inventory determine completed coverage.

## IPv4 range-next extension boundaries

The independent `RangeMath` model uses inclusive raw numeric endpoints mapped to
Empty or `Live(start,stop+1)` in Nat. Its next transition does not reference the
extracted iterator. The inductive type also permits malformed Live values, but
public range interpretations are always `ofInclusive` of bounded octets; its
`live_bounds` theorem supplies the nonempty half-open invariant. No additional
precondition is required on raw range inputs. The independent model and its
partition/size/no-revival helpers were reviewed against range-next-specification.md;
these helpers alone are not implementation verification.

| Connection | Classification and exact observation |
| --- | --- |
| `core::mem::replace` | Existing Aeneas standard-library model `Aeneas.Std.core.mem.replace` in `Std/Core/Core.lean`: `(dst,src)` returns the old value and updated new destination. This is a baseline trusted Rust/state-translation boundary, not a new extracted proof of Rust pointer operations. The actual next proof must connect both results to the returned range fields. |
| `core::num::U32::saturating_add` | Existing Aeneas scalar model `Aeneas.Std.core.num.U32.saturating_add` in `Std/Scalar/SaturatingOps.lean`. Its mathematical meaning is clamp to U32 MAX. New theorem `core.num.U32.saturating_add_val` proves from the unchanged model definition that the numeric result is `min(x.val+y.val,2^32-1)` for all U32 inputs. This is a kernel proof about the baseline trusted scalar model, not new Rust/model correspondence proof. |
| ipnet IPv4 `IpStep::add_one`, `replace_zero`, `replace_one` and `Ipv4AddrRange::next` | Must remain actual extracted bodies, composed with the existing conversion/comparison/state models. Independent statement/body review completed below; final verifier evidence remains separate. Do not classify the independent desired transition as a replacement implementation. |

Astra reviewed the SaturatingOps diff: the accepted semantic addition is the
value theorem above, using unfolding, BitVec numeric reduction and `omega`.
The saturating-add definitions themselves are unchanged. Visibility/exposure
metadata, if required for downstream proof access, does not alter their meaning.
The Less branch must derive non-saturation from `start<stop<2^32`; the Equal
branch must show actual sentinel `(1,0)` is empty. Thus neither MAX nor zero
singletons may be removed from public scope to accommodate helper arithmetic.


### Range-next independent implementation review

Astra reviewed `RangeNext.range_next_spec` and helpers against the frozen
range-next specification. For every raw range, it proves actual generated next
returns normal success with both returned-address numeric observation and updated
remaining state equal to the independent transition. Less derives `s+1≤MAX`
from `s<e<2^32`; Equal returns the original address and installs `(1,0)`;
Greater returns None with the original range. No raw input states are excluded.
`RangeNext.constructor_remaining` connects the actual raw constructor to the
same abstract interpretation for all address pairs.

`RangeLaws.next_none_iff_empty`, `next_some_laws`, `next_empty_preserved`,
`next_none_no_revival`, and `finite_no_revival` connect the actual next result to emptiness, exact head,
one-unit size decrease, disjoint singleton/residual partition, and preservation
of exhaustion on a subsequent actual call. Their conditional success parameters
are justified by the unconditional `range_next_spec`; no termination obligation
is replaced by a success assumption. `finite_no_revival` explicitly constructs `NoneSteps` for any Nat count; each
step is an actual normally returning next call. Its induction rules out revival
after any finite number of additional calls. This review covers those
semantic statements and dependencies; the integration build/axiom audit and full
verifier evidence remain the final reproducibility checks.

## IPv4 API expansion: Result-to-Option boundary

The new model `Aeneas.Std.core.result.Result.to_option` in `Std/Core/CoreResult.lean`
is registered only for `core::result::Result::ok`. It returns outer normal
success with `some value` for Rust Ok and `none` for Rust Err. Pinned
`core/src/result.rs:709–717` performs the corresponding direct variant match.
The source hash is recorded in `std-source-boundaries.json` and checked by the
runner. Narrow extraction of `Result::map` remains selected; this model does not
replace map or the ipnet supernet body.

Classification: **reviewed trusted Rust/model correspondence**, limited here to
`Result<Ipv4Net, PrefixLenError>::ok` and, in the IPv6 expansion,
`Result<Ipv6Net, PrefixLenError>::ok` in the actual supernet paths. Both network
types are drop-free stored-address/prefix values, and PrefixLenError has no fields.
The IPv6 use is reviewed under the same pinned match and discard behavior;
it does not require a change to the model or its registration. Although the Lean
model and registration are polymorphic, this review does not establish its Rust
correspondence for arbitrary error types with effectful or panicking destructors.
The Err payload discard in generic Rust is a real operation; the concrete
selected use has no destructor effect. The reviewer inspected the model's two
branches and the pinned source; no Lean proof of source/model correspondence is
claimed. Actual supernet total success, including `/0` returning None, must still
be established by the application theorem and audited with the final evidence.

### Incremental IPv4 network API review

Astra reviewed the first four completed `IPv4NetOps` statements against
ipv4-api-specification.md: `default_spec`, `from_ipv4_spec`, `hosts_spec`, and
`subnets_spec`. Default gives numeric zero/prefix zero; From preserves exact
address/prefix 32. Hosts covers every valid, possibly noncanonical network and
specifies both raw numeric endpoints and independent remaining state. The pure
`IPv4NetMath.hosts_remaining_lt31` / `hosts_remaining_ge31` bridges show exactly
`[lo+1,hi)` or `[lo,hi+1)`, including `/0`, `/31` and `/32`; the adjustment
bounds establish no lost endpoint through saturation. Subnets includes all U8
requested prefixes, exact ordinary error branches, and exact successful
start/end/minimum-prefix state. It proves construction only, not subnet iteration.

The public address-minus-U32 helper `IPv4NetOps.ipv4_saturating_sub_spec` also
states the full-domain actual trait contract with Nat truncated subtraction and
normal success. It is eligible for its own precisely labeled public mapping;
its scalar subtraction lemma remains a helper about the existing Aeneas model.
No additional assumptions on host bits, nonempty ranges or arithmetic safety
appear in these statements. Supernet, sibling and other APIs are not approved
by this incremental review; their later final statements require separate review.


### Supernet, sibling, and range-observer statement review

Astra independently approved `IPv4NetOps.supernet_spec` and `is_sibling_spec`.
Supernet covers `/0` returning None and all positive valid prefixes returning a
canonical immediate parent with exact prefix/address and child-set containment.
Sibling is exactly positive equal prefixes with equal parent lower values,
including self comparison and unequal stored addresses representing one child.
`IPv4NetMath.parent_contains_child_iff_same_parent` supplies the independent
Nat set/parent bridge; no implementation observation defines that model.

The current `RangeMore` reviewed contracts are `range_next_back_spec`,
`range_last_spec`, `range_max_spec`, `range_min_spec`, `range_count_u64_spec`,
`range_count_spec`, and `range_size_hint_spec`. Back returns and removes the
last element in the same total-success theorem for every raw endpoint pair.
The consuming observers return exactly the independent first/last options.
Count and size_hint cover all raw inputs, including length `2^32`, under explicit
`System.Platform.numBits=64`; this is a platform condition, not a shortened
range domain. Count_u64 is a helper. The two full-domain address subtraction
statements preserve their distinct address/scalar output types and are suitable
for separately labeled public arithmetic mappings. Skip methods and additional
mixed-operation laws are not approved merely by this incremental review.

## Optional IPv4 mask parsing dependency review

Astra inspected the current regenerated `Ipnet.lean`: `core.num.U32.leading_ones`
is an actual extracted body computing bitwise complement and calling
`leading_zeros`; `mask.ipv4_mask_to_prefix` is the actual conversion → leading
ones → checked shift → unwrap-or-zero → zero-test body; `Ipv4Net.with_netmask`
is the actual result propagation and constructor body. No handwritten replacement
for those operations is used and no generated axiom was found in this inspection.
This extraction review does not establish the mask-contiguity iff contract;
that requires the later application theorems.

| Selected dependency | Correspondence classification and precise meaning |
| --- | --- |
| `core::num::U32::leading_zeros` | Existing baseline trusted Aeneas scalar model, registered by `ExtractBuiltin.ml`; `Std/Scalar/LeadingZeros.lean` defines `BitVec.leadingZeros x = if x=0 then w else w-Nat.log 2 x.toNat-1`, then packs this Nat into U32. It is not the core Lean `BitVec.clz` implementation. Lemmas about its bound/log formula are kernel model proofs, not Rust intrinsic correspondence proofs. Pinned uint_macros source identity is checked by the runner. |
| `core::num::U32::leading_ones` | Actual extracted `(!self).leading_zeros()` from the pinned uint_macros source. Bitwise complement uses the existing scalar/BitVec operation, and leading-zero semantics retains the preceding baseline trust. |
| U32 `checked_shl` / `unchecked_shl` | Actual extracted branch checks rhs<32, otherwise ordinary Some/None behavior; supported U32.shl delegates to the existing checked shift model. The previously recorded runtime-UB/Miri-sysroot compatibility and safety obligations remain unchanged. Prefix 32 must take None and cannot be treated as a successful in-range shift. |
| `Option<U32>::unwrap_or` | Existing `Aeneas.Std.core.option.Option.unwrap_or` model in `Std/Core/Core.lean`: Some payload or supplied zero default on None. Concrete values are drop-free; no generic destructor guarantee is inferred. This is baseline model correspondence, not a newly extracted Option implementation. |

Astra independently approved the final `IPv4MaskOps.ipv4_mask_to_prefix_spec`
and `with_netmask_spec` against the frozen optional mask specification. Both
establish actual-body normal success, Ok exactly for each U8 prefix satisfying
`p≤32 ∧ ipv4Value(mask)=2^32-2^(32-p)`, and Err exactly when no such prefix
exists. Thus all noncontiguous patterns are rejected. The constructor preserves
the original address structurally, including every host bit. The checked shift
bridge explicitly handles prefix 32 as None followed by the zero default; only
prefixes below 32 use a successful shift. Prefix bounds, exact U8 casting and
uniqueness connect to independent Nat modular-arithmetic and logarithm lemmas
in `IPv4MaskMath`, without assuming parser correctness. Zero and all-one masks
remain covered. This review approves the two contracts; final reproducible build
and transitive audit remain required for accepted coverage evidence.


### Final IPv4 range expansion review

Astra independently reviewed the completed `RangeMore` contracts for next_back,
nth, nth_back, count, size_hint, last, min, and max. The skip contracts quantify
over all raw endpoint states and all Usize indices under the explicit 64-bit
platform condition. They jointly establish normal return, exact optional value,
and independent remaining interval. Out-of-range skips consume the remaining
range; final-element skips return that element and exhaust; intermediate skips
remove exactly the skipped elements and returned element. `skipFront` and
`skipBack` agree with the frozen half-open specification, including full IPv4
length `2^32`, MAX singleton, reversed endpoints, and indices above U32 range.
The proof establishes cast bounds in the successful branch rather than imposing
them on callers. No additional model boundary is introduced by these bridges.

`range_empty_no_revival` establishes actual normal None plus abstract empty
state for each of next, next_back, nth and nth_back from every raw empty state.
Its four conclusions can be repeatedly applied to mixed sequences; it does not
require an identical concrete empty representation. The theorem itself is a
one-step closure law, not a separately formalized finite mixed-sequence theorem.
The two public subtraction contracts retain full-domain truncated subtraction
with address and U32 outputs respectively. Final build, inventory and transitive
axiom audit remain the reproducibility gate for this reviewed scope.


### Final IPv4 bitwise API review

Astra independently approved `BitOps.ipv4_and_addr_spec`, `ipv4_and_u32_spec`,
`ipv4_or_addr_spec`, and `ipv4_or_u32_spec`. Each targets the actual extracted
public trait method, establishes normal success for every input, and gives the
exact independent big-endian address value as Nat AND/OR. Both RHS types are
covered and all four Rust output types are Ipv4Addr. Existing checked address
conversion and scalar bitwise bridges provide the connection; no new semantic
model boundary was added. The local trait extraction selectors name IpBitAnd
and IpBitOr with concrete Ipv4Addr self type, while required generated definitions
pin both RHS specializations. Scalar helper lemmas and trait declarations are
not counted as additional API contracts. Final reproducibility and axiom audit
remain the evidence gate.

## IPv4 subnet trailing-zero boundary

The selected new model is only `Aeneas.Std.core.num.U32.trailing_zeros` in
`Std/Scalar/LeadingZeros.lean`, registered for the exact U32 Rust operation.
It returns the existing leading-zero count of the fixed-width 32-bit reversal
of the operand. Independent review checked the pinned uint_macros implementation
(`intrinsics::cttz`) and its specified zero result of 32. BitVec.reverse maps
bit i to bit 31-i, so this model counts exactly the low-order zero run, with
zero→32 and MAX→0. Classification: reviewed trusted Rust intrinsic/model
correspondence; no kernel proof of the Rust intrinsic is claimed. Kernel lemmas
about this model must still connect its count to the independent divisibility
and greatest-fitting-block specification before subnet coverage is accepted.

`U32::trailing_ones` remains the actual extracted complement-then-trailing-zeros
body from the pinned uint_macros source, rather than a second new model. Its
zero→0 and MAX→32 behavior follows through that body and the preceding boundary.
The existing leadingZeros logarithmic model and scalar complement retain their
previously recorded trust classification. Source hash checks establish source
identity only. No generated body is edited and no custom axiom is permitted.

Astra reviewed `IPv4SubnetBits`: `lz_eq_clz` proves the logarithmic leading-zero
model equal to Lean's bit-count operation, then `trailing_zeros_value` uses
fixed-width reversal to connect the registered normal-result model to ctz.
`trailing_zeros_mod_spec` proves, for every U32 input and j≤32, that j is at most
the count exactly when the input value modulo 2^j is zero. Zero, MAX, j=0 and
j=32 are included. These are kernel model bridges; the intrinsic correspondence
classification above is unchanged. `IPv4SubnetMath` independently defines the
least eligible prefix and proves its equivalence to greatest admissible dyadic
height, canonical block membership, exact residual partition and strict Nat
length decrease. These helper reviews do not yet certify actual subnet iteration
or complete fixed-prefix enumeration.

## Final IPv4 subnet iteration and trace review

Astra independently approved `IPv4SubnetAll.next_raw_spec` as the single public
Ipv4Subnets::next mapping. It has no input restriction and classifies all raw
states: reversed endpoints return normal None unchanged for every U8 prefix;
live states with q≤32 return the exact greatest fitting aligned block, exact
independent residual interval and unchanged q; live states with q>32 take the
modeled unwrap panic path. Invalid-prefix failure is an explicit contract, not
ordinary-success coverage. Branch theorems remain helpers rather than three
additional API counts. Full range, arbitrary unaligned start, zero/MAX singleton
and noncanonical constructor-originated networks remain included.

`IPv4SubnetEquality` connects the actual extracted address PartialEq body to
the existing Aeneas Array/Slice elementwise equality models, then to independent
numeric equality through `IPv4AddressEq`'s base-256 injectivity proof. This uses
existing baseline array/slice/U8 equality correspondence, not a new comparator
model. `IPv4SubnetStateMath` proves the saturated and unsaturated residual
relations and singleton exhaustion, and `IPv4SubnetIterator.next_live_spec`
connects those facts to all branches of the actual next body. The only new
intrinsic boundary is the reviewed trailing-zero model described above.

Astra also approved the unconditional `IPv4SubnetActualTrace` corollaries.
`liveLaw_checked` discharges the earlier explicit LiveLaw premise using the
actual next_live_spec theorem; no correctness premise remains in the final
trace theorems. ActualTrace records every normal Some call and the terminal
normal None call. Finite Nat length bound, exact union, canonical outputs,
ordered disjoint blocks and minimum-prefix preservation are connected to those
calls. `constructor_fixed_trace` starts from the actual subnets constructor and
proves the exact indexed list and count 2^(q-p) for every valid possibly
noncanonical input and p≤q≤32. Logical finite lists do not claim allocation or
runtime collect success. Final reproducible build/audit remains the acceptance
gate, and aggregate/parser/other unselected consumers remain outside this scope.

## IPv6 iteration: standard segment constructor

The continuation selects a narrow executable standard-library model,
`ipnet.core.net.ip_addr.Ipv6Addr.new`, in
`.tools/aeneas/backends/lean/Aeneas/Std/NetIpAddr.lean`. Eight U16 arguments
normally produce an address whose sixteen octets concatenate the eight existing
U16.to_be_bytes results, in argument order. It applies to all segment values.
The rust_fun registration is specific to the concrete core Ipv6Addr constructor;
it does not model generic transmute, ipnet IpStep, or an iterator application body.

Pinned extraction Rust nightly-2026-09-17 core/src/net/ip_addr.rs:1377–1392
converts each segment with to_be, then transmutes the eight words to sixteen
bytes. On the pinned little-endian target, swapping each word before taking its
native byte representation yields the high byte then low byte exactly once.
The already recorded source hash in std-source-boundaries.json covers this body.
An earlier investigation's February-toolchain line reference was rejected and
corrected before integration; it is not the source of the accepted correspondence.

Classification: reviewed trusted Rust/layout/model correspondence. Kernel proofs
of the executable model's independent numeric value establish its mathematical
behavior, not the Rust memory-layout correspondence itself. The default native
boundary tests include asymmetric segments, zero and all-ones values; they are
finite observations and not a replacement for proof or source review. Acceptance
of the new model and dependent application contracts requires the full verifier's
exact patch/binary checks, fresh extraction and transitive axiom audit.

The constructor selector also requires a small Charon compatibility fix: the
inherent-implementation matcher now applies its existing `matches_ty` function
to `bound_ty.skip_binder`, replacing the previously unconditional false/TODO.
This controls extraction selection, not application semantics. Independent
review covers the concrete region-free address types used here, not arbitrary
generic binder matching. The official `sol-ipv6-range-all9-matcher` probe retains
actual IPv4 new and both families' to_bits/from_bits bodies while making only
the exact IPv6 new call use its registered model. No unresolved generated axiom
is accepted. Baseline 403 tool patches/pins are archived with hashes under
verification/runs/baseline-403-tool-snapshot for prior-checkpoint recovery.

## IPv6 subnet bit-count boundary

`Aeneas.Std.core.num.U128.trailing_zeros` in `Std/Scalar/LeadingZeros.lean`
returns normal `Result.ok` of a U32 containing `BitVec.leadingZeros x.bv.reverse`.
The bitvector has fixed width 128, so zero returns 128 and all-ones returns 0.
The rust_fun registration is exact to the U128 primitive. This extends the
previously reviewed U32 cttz boundary to the source's actual 128-bit operation.
Astra reviewed the pinned uint_macros cttz source and the same fixed-width
meaning. Rust intrinsic/model correspondence remains reviewed trusted; the
bit/divisibility/maximal-block lemmas and actual subnet body must still be
kernel checked. Actual U128 trailing_ones is extracted, not replaced. The
subnet probe output2 has no unresolved axiom but is not by itself an API proof.
The new U128 saturating-add/sub value lemmas describe the unchanged existing
scalar models and do not introduce another executable semantic model.

The U128/Usize maximum-plus-one failure lemmas are kernel proofs about the
unchanged checked scalar tryMk/add semantics, not extra Rust models. They
support the explicit count overflow contracts; no release-profile overflow
behavior is inferred.

The final IPv6SubnetActualTrace theorems discharge LiveLaw using the actual
next_live_spec. Every Some call and the terminal None call are represented;
canonicality, ordered disjoint exact partition and fixed-origin index/count
laws apply to these actual calls. Lengths are mathematical Nat values up to
2^128, not a promise that a Vec can be allocated or collected successfully.
The full raw one-step contract separately covers reversed ranges at every q
and the live invalid-q panic. No new model is introduced by this composition.

## Tagged naming and remaining value contracts

The post-588 continuation adds a Lean-only binder-allocation collision check
against existing ordinary dotted declaration roots. This alpha-renames local
mask parameters through the existing name map and preserves actual function
bodies. The reviewed scope does not assert universal hygiene for strict-name
sets or other backends. It introduces no executable standard-library model.
Tagged mask contracts compose existing concrete mask models and actual IpNet
constructor dispatch, including cross-family address-width validation.

Tagged Clone/eq/cmp/partial_cmp contracts compose prior concrete stored-value
proofs and the actual enum branch/discriminant bodies. The new_assert invalid
branch uses the unchanged massert model's assertionFailure tag, distinct from
unwrap panic. These are runtime model contracts, not const-checking, formatting,
or unwinding equivalence claims. Error singleton clone/equality bodies are
independent of the unverified parser and Formatter paths.

To expose the existing Unit clone equation, Std/Core/Core.lean marks the
unchanged BuiltinClone definition @[expose] and adds builtinClone_unit_spec by
rfl. The clone/clone_from bodies and registrations are unchanged. This supplies
a concrete kernel equation for actual AddrParseError::clone composition; it
is not a new generic Rust Clone correspondence claim.
