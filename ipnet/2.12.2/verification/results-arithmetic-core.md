# Local verification results — ipnet 2.12.2

Accepted run: **2026-10-16**, [check-3qKltBRf](runs/check-3qKltBRf/result.json).
The complete version-local verifier passed: **36 public API contracts and 83
helper theorems**, 119 audited theorems total. This extends the original 15-API
run, preserved in [results-initial-core.md](results-initial-core.md). It does not
complete whole-crate verification or the expert's containment/partition/aggregate goals.

## Formal coverage

| Scope | Public API mappings | Contract |
| --- | ---: | --- |
| Ipv4Net, Ipv6Net, IpNet: new, new_assert, addr, prefix_len, max_prefix_len | 15 | Exact construction/error and stored observations |
| Ipv4Net, Ipv6Net, IpNet: netmask, hostmask, network, broadcast, trunc | 15 | Total success and independent CIDR integer formulas for every valid prefix |
| From<Ipv4Net>, From<Ipv6Net> for IpNet | 2 | Exact family-preserving conversion |
| Ipv4AddrRange::new, Ipv6AddrRange::new, Ipv4Subnets::new, Ipv6Subnets::new | 4 | Exact argument storage for all raw input states |

For address width w and valid prefix p, independently define K = 2^(w-p),
lo = (a/K)*K and hi = lo+K-1 in Nat. The arithmetic contracts prove returned
address values equal 2^w-K (netmask), K-1 (hostmask), lo (network), or hi
(broadcast). trunc returns the same prefix and an address of value lo. IpNet
preserves the address family. The address interpretation is a recursive
network-byte-order octet value, independently connected to generated conversions.
No alignment or zero-host-bit precondition is imposed: /0, /w and noncanonical
stored addresses are included, with width-boundedness proved from the bytes.

The original new contracts include every u8 prefix and exact ordinary Rust
Err(PrefixLenError) for invalid prefixes. new_assert proves success only on
valid prefixes; invalid-prefix panic behavior is outside these contracts.
The four raw iterator constructors prove storage only, including reversed
endpoints and arbitrary prefix bytes; they do not prove any iterator transition.

Astra independently specified and reviewed the contracts; Sol authored the
implementation proofs and consulted Astra as oracle. The primary reviewed
coverage, tool patches, evidence and the full verifier. See
[specification.md](specification.md),
[set-operations-specification.md](set-operations-specification.md),
[theorems.json](theorems.json) and [proofs.toml](../proofs.toml).
The 83 helper theorems include CIDR arithmetic, tagged endpoint/subset laws,
byte/integer bridges and bitwise identities. Helpers are not additional public
API coverage, and model-only containment laws are not a proof of contains.

## Reproducible checks

- Registry archive checksum, embedded release commit, captured source inventory,
  clean upstream submodule/Gitlink, tracked source bytes and Cargo build surface.
- Exact tool/dependency revisions, recorded compatibility diffs and tool binary hashes.
- Fresh shared extraction and byte comparison of every maintained generated model.
- Local Lake package clean, rebuild, theorem-kind and transitive axiom audit:
  **119/119 passed**, with all 36 public mappings checked against proofs.toml.
  Only propext, Classical.choice and Quot.sound are permitted; no sorryAx,
  application axiom or native-decision axiom was accepted.
- Eight kernel-checked shift boundary examples cover U32/U128 left/right shifts:
  width-1 succeeds exactly; width fails with integerOverflow.
- Identical before/after input fingerprints, including specifications, proof files,
  tests, patches, tool binaries and shared extraction/audit scripts.
- Separate native tests, each under default and no-default-features:
  **33 unit + 6 integration + 56 doc tests passed**. The six independent CIDR
  suites exercise containment, aggregation, ranges, hosts and subnet partition.
  They are finite observations and do not extend formal coverage. Formal
  extraction uses default features on the pinned host.
- Shared extraction/audit helper regression tests: 10 passed separately.

## Bugs recorded for future upstream PRs

[Bug records and reproduction instructions](bugs/README.md) contain pinned,
standalone Rust schema generation, actual serde output, independent JSON Schema
validation, saved counterexamples and hashes. These are native reproductions,
separate from the Lean audit.

**IPNET-001 confirmed:** both schemars08 and schemars1 integrations generate an
IpNet schema that rejects valid serialized IPv4 networks, including
192.168.0.0/24 and 0.0.0.0/0. Both oneOf branches match because the IPv6 regex is
too broad. A future regression mode currently fails on this output-conformance
requirement. **IPNET-002:** a/64 is accepted by the generated schemas and rejected
by actual parsing/deserialization; exact schema soundness is a separate contract
for upstream discussion. No CIDR regression failure was observed in the finite
suites. The pinned ipnet implementation remains unchanged. No issue or PR was published.

## Source, tools and trust boundaries

The official registry index selected 2.12.2 as the latest non-yanked stable release
on 2026-10-16; published 2026-09-06. Registry archive checksum:
791930b43c0d5973160d90a8f3894509f2b273430f5c5c73b668636d0287c5c0.
Upstream commit: 13c5c5873c02127679b1e8e64b538e4e36942640.

Aeneas 8e62dc3dc765602833c86b68dceb18a475a50a8f, Charon
08d7c9d50144bd84848212c24701253585e90d1f, proofs-rs
a2335432635301597f203e1159e3d16888ce2333 (cargo-proofs 0.4.1), extraction Rust
nightly-2026-09-17, native Rust 1.91.1, Lean 4.35.0, macOS arm64.
[toolchain.json](toolchain.json) records exact binaries and compatibility patches:

1. Existing proofs-rs reserved audit-identifier correction.
2. Charon lowers only recorded true-valued UbChecks and recognizes the divergent
   panic_nounwind_fmt helper. False-valued unsupported extraction remains rejected.
3. Aeneas checked shift-name wrappers, exact erasure of the unused unwrap Debug
   dictionary, corresponding generated registration metadata, and a one-line
   correction comparing trait-filter length against trait clauses rather than
   type parameters. The original Formatter model is unchanged. The original and
   dictionary-free unwrap models are proved equal on both branches in patched
   Std/Core/Fmt.lean. Aeneas's OCaml executable was rebuilt and pinned.

Astra reviewed these semantic changes, including token-level comparison of the
large generated metadata formatting diff. The first expanded audit rejected
trunc's Formatter dependency; the precise erasure route resolved it before the
accepted fresh run. The final generated ipnet model was never hand-edited.
Exact patches are enforced for dedicated tools and the actual Lake dependency.

Trust remains in Rust-to-LLBC-to-Lean translation, the reviewed tool patches,
selected Aeneas scalar/big-endian byte conversion models, the Lean kernel and
source/tool provenance checks. Pinned Charon uses a Miri sysroot, so optional
language-UB diagnostic checks may be skipped; proofs discharge the actual shift
bounds independently. LLBC settings are checked (UB/overflow true, contract
checks false). Claims are about runtime methods under these model choices,
not general const-evaluation, abort/unwind observables, compiler equivalence or
all platforms. See [extraction-notes.md](extraction-notes.md).

## Remaining unverified scope

- Actual contains trait bodies and their specialized public dispatch: probes
  reach IPv4 array/slice comparison mismatches and IPv6 segments transmute.
  No axiom-bearing probe is accepted. Mathematical subset helpers do not resolve
  these implementation boundaries.
- supernet/is_sibling, with_netmask/from_bitmask, prefix/mask parsing and related APIs.
- Range next/next_back/nth/nth_back and all other iterator transitions, hosts,
  Net::subnets partition, raw Subnets iteration and aggregate union preservation.
- Parsing/formatting, remaining conversions/traits, serde/schema contracts,
  optional integrations and alternative platforms.

These remain obligations under the independent specification. Extraction failures
for particular probes are not a claim that every untried API is blocked.

## Evidence identity and reproduction

Run `bash ipnet/2.12.2/scripts/verify.sh` from the repository root. Runs are
preserved locally under ignored verification/runs directories; rejected and
historical runs were not overwritten. No login, push, cargo-proofs recording,
upload or publication occurred.

- Complete result SHA-256: 4a3d117d55a0484d8785d419dcee9666cfb87b0df0a11c45bdcb1f71261a99d1
- Input fingerprint SHA-256: b529a560ac4f6e4bb969232790c31c2b7a88054af4c8bc160cd15b8654921130
- Audit result SHA-256: 3680597a391d7fab177c6b2b2060c46bb77b219f1d3fc9ff8a20aa8849f12efa

The result JSON records individual artifacts/log hashes. This post-run summary
is intentionally outside the input fingerprint; standalone schema evidence has
its own hash ledger in bugs/schema-repro/evidence.json.
