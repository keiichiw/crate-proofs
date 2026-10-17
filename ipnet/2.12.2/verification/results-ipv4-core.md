# Local verification results — ipnet 2.12.2

Accepted run: **2026-10-16**, [check-bu0Pgyqd](runs/check-bu0Pgyqd/result.json).
The complete verifier passed with **243 audited theorems: 66 public contracts
and 177 helpers**. This continuation adds **23 IPv4 public contract mappings**
to the preceding 43. Astra independently specified/reviewed the contracts; Sol
agents proved actual extracted bodies; the primary reviewed mappings, model
boundaries, source/tool identity and the full local evidence.

This remains partial API coverage under the explicit standard-library model
correspondences below. It is not whole-crate or unrestricted cross-platform
verification. See the [IPv4 coverage ledger](ipv4-coverage.md) for remaining APIs.

## New IPv4 contracts

The [independent specification](ipv4-api-specification.md) fixes full input domains
and mathematical observables before implementation proof. All selected contracts
establish normal outer Aeneas success; Rust Err results are ordinary outputs.

| Group | New public contracts | Guarantees |
| --- | --- | --- |
| IPv4 range (8) | next_back, nth, nth_back, count, size_hint, last, min, max | Exact numeric observations; returned option and updated half-open interval together for mutable operations |
| IPv4Net (6) | hosts, supernet, is_sibling, subnets, Default, From<Ipv4Addr> | Exact independent endpoints/parent relation, error cases and stored values |
| Mask conversion (2) | ipv4_mask_to_prefix, Ipv4Net::with_netmask | All-input success/error iff contiguous-mask formula, exact original address retained |
| Public arithmetic/bitwise (7) | IpAdd<u32>; IpSub<u32>/IpSub<Ipv4Addr>; IpBitAnd and IpBitOr with u32/address RHS | Exact saturating arithmetic and independent numeric bitwise results |

### Range domains and platform scope

All raw endpoint pairs are included: reversed, singleton zero/MAX, arbitrary
addresses and the full IPv4 interval. Remaining state is Empty or Nat `[s,e+1)`;
its length may be 2^32. next_back returns the final element and removes it.
nth/nth_back either return and consume the indexed element plus skipped elements,
or return None and empty the range. Large indices are not assumed to fit U32.
The internal casts and nonsaturating arithmetic are justified from branch bounds.

The four Usize-sensitive contracts — count, size_hint, nth, nth_back — explicitly
assume **System.Platform.numBits = 64**. Every Usize value is covered on that
platform, including its maximum. count gives exact length and size_hint gives
`(L,Some L)`. No claim that full-range count succeeds at 32 bits is made.
Endpoint observers and next_back require no additional input-domain restriction.

The derived empty-preservation theorem connects actual next, next_back, nth and
nth_back calls: each returns None and stays abstractly empty after exhaustion.
This is a one-step closure for all four operations, usable repeatedly; it is not
reported as a separate formal theorem about arbitrary mixed command sequences.
The preceding next proof and finite-next no-revival theorem remain audited.

### Networks, masks and overloads

Network operations accept every valid prefix and arbitrary original host bits.
hosts excludes network/broadcast for p<31, includes both addresses at /31, and
the single address at /32. supernet returns None at /0 and otherwise the canonical
immediate parent, with a proved child-set containment relation. is_sibling means
positive equal prefixes and equal immediate parent sets; self-comparison may be
true. It does not establish that the two canonical children are distinct.

subnets handles every U8 argument: exact PrefixLenError when q<p or q>32,
otherwise the correct raw start/end/minimum-prefix state. **This is initialization
only, not subnet enumeration or partition.** Default gives zero/0; From preserves
the exact address and sets prefix 32.

Mask validity is the independent formula `p≤32 ∧ value(mask)=2^32-2^(32-p)`.
Both APIs prove exact Ok/Err equivalences for every mask, including noncontiguous
patterns, all-zero /0 and all-one /32. with_netmask preserves the exact supplied
IP including host bits. This is mask conversion, not textual address parsing.

Arithmetic addition is min(A+d,2^32-1); subtraction is Nat truncated subtraction.
The address-RHS subtraction returns U32, while scalar-RHS subtraction returns
an IPv4 address. The four bitwise methods return addresses whose independent
network-order values equal Nat AND/OR. Internal IpStep and scalar helpers do not
inflate public API counts.

All previous 196 theorem identities and 43 public mappings are retained and
reaudited. The already-proved `RangeNext.ipv4_saturating_add_spec` is intentionally
reclassified from helper to public contract because it proves the real exported
IpAdd implementation; it is not counted as a newly invented theorem. Earlier
coverage is archived in [results-range-next.md](results-range-next.md),
[results-containment-core.md](results-containment-core.md), and the earlier
arithmetic/core reports. Using the existing convention for generic contains
specializations, 66 contract mappings correspond to 63 API forms.

## Explicit model and tool trust

The [model ledger](model-boundaries.md) distinguishes kernel proofs about selected
models from reviewed Rust/model correspondence. Existing concrete address type
and Ord::cmp models, default PartialOrd::le, scalar/byte/memory models and
Rust-to-LLBC-to-Lean translation remain trust boundaries. Rust comparator bodies,
IPv6 segments/transmute and generic pointer semantics are not independently proved
by this expansion.

The only new semantic model is Result::ok as a two-variant match: Ok becomes Some,
Err becomes None. Narrow extraction of the actual Rust ok body hit an Aeneas
bottom-value translation failure. Astra reviewed the replacement against pinned
core/result.rs, restricted to the drop-free Result<Ipv4Net,PrefixLenError> use.
It is **reviewed trusted correspondence**, not a proof of arbitrary generic Rust
Result::ok with effectful destructors. Result::map remains an actual extracted body.
The pinned source hash is checked by the verifier.

A kernel lemma gives the exact numeric value of the existing unchanged U32
saturating-subtraction model. It adds no semantic assumption. The mask route
extracts actual leading_ones, checked_shl, the parser and with_netmask bodies;
leading_zeros uses the existing Nat-log scalar model and unwrap_or its existing
option model. Bitwise methods use existing scalar models and proved conversion
bridges. No new mask, bitwise or iterator model replaces an ipnet implementation.
The independent transition/mask specifications are connected to actual bodies.

Tool revisions and the 64-bit aarch64-apple-darwin extraction configuration remain
pinned. Exact compatibility patches and actual Lake dependencies are checked.
The updated Aeneas executable hash is recorded in toolchain.json, and the combined
patch SHA-256 is 06ea07b09a8e3f582e7005db0ab86b9d6bbabe8df4727cf5b44a20beeca77b35.
See [extraction-notes.md](extraction-notes.md) for rejected probes, selection rules
and Miri/runtime-check limitations. No general const-evaluation, abort/unwind,
compiler-equivalence or other-platform guarantee is claimed.

## Checks and reproducible evidence

- Unchanged ipnet 2.12.2 release source at commit
  13c5c5873c02127679b1e8e64b538e4e36942640; archive checksum
  791930b43c0d5973160d90a8f3894509f2b273430f5c5c73b668636d0287c5c0.
  Latest stable version was resolved on 2026-10-16; pins were not upgraded mid-proof.
- Source inventory, Gitlink, Cargo build surface, tool revisions, binary hashes,
  exact tool patches and six reviewed Rust core source hashes passed checks.
- Fresh shared extraction matches every maintained generated Lean file byte-for-byte.
  Generated axioms, sorry and partial unsupported bodies remain forbidden.
  Concrete IPv4 bitwise selectors avoid selecting unrelated IPv6 overloads.
- Local proof package cleaned and rebuilt, with **243/243** theorem/mapping and
  transitive axiom checks passed. Only propext, Classical.choice and Quot.sound
  are allowed; no sorryAx, application axiom or native-decision axiom accepted.
- Eight kernel-checked shift examples passed.
- Native default and no-default-features tests separately passed, each with
  **33 unit + 15 integration + 56 doc tests**. New finite cases cover raw ranges,
  maximal skip indices, all prefixes, all U8 subnet arguments, mask bit flips,
  public arithmetic saturation and asymmetric-byte bitwise operations. These
  tests do not replace universal proofs.
- Shared extraction/audit helper test suite: 41 tests run, one skipped, no failures.
- Before/after input fingerprints match. Every recorded artifact hash and the
  current input fingerprint were independently rechecked after completion.

## Remaining work and bug findings

The main remaining IPv4 work is Ipv4Subnets::next and full subnet partition,
Ipv4Net::aggregate union/minimality, textual parsing/formatting, unmapped traits
and generic iterator consumers, and serde/schema/optional integrations. Raw subnet
construction and network subnets initialization do not prove iteration. Generic
collection allocation and invalid-prefix panic domains remain excluded. IPv6/enum
range iteration is not covered by the IPv4 contracts. See the detailed coverage
ledger; an empty extracted-but-unproved list is not whole-crate verification.

No new ipnet implementation bug was found in this continuation. Existing schema
counterexamples remain in [bugs/README.md](bugs/README.md) with reproductions for a
future upstream PR. No issue, PR, login, push, upload or publication occurred.

## Reproduce and identify this run

Run `bash ipnet/2.12.2/scripts/verify.sh` from the repository root. Evidence stays
local under the ignored verification/runs directory.

- Complete result SHA-256: dee4e833ae5afc5672cc3aa7575ef21c689c93b9161fef8348daed8d3ae4424e
- Input fingerprint SHA-256: 859d6e24e232c264f8559b4c872131d130ed7c2ba0679c0d0067f46387d8699e
- Audit result SHA-256: 100613fb9784391ba7fe42f6bc6e49e202203921a97876677fcacd6f5ef00a74

The result JSON records individual artifact hashes. This post-run summary is
excluded from the input fingerprint. Historical reports retain original evidence
identities and do not describe the newly extended scope.
