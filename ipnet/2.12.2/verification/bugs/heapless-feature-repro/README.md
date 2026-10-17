# IPNET-003: heapless feature misses stack-buffer serialization

Confirmed against unchanged ipnet 2.12.2 source with Rust 1.91.1. The documented
`heapless` feature enables serde and promises allocation-avoiding serialization,
but `ipnet_serde.rs:87–94` guards its IPv4 stack buffer only with `ser_as_str`.
Cargo's `heapless` feature does not enable that legacy feature. The analogous
IPv6 branch has the same guard; this reproduction directly tests IPv4 only.

The custom human-readable Serializer accepts only the exact expected string,
returns its length without allocating, and inherits serde's default collect_str.
Pinned serde_core 1.0.229 `src/ser/mod.rs:1373–1377` implements that default with
`self.serialize_str(&value.to_string())`, which allocates. Allocation/reallocation
counts are reset after parsing and captured before printing. Both configurations
serialize the same original network and verify the exact same 18 output bytes.

From repository root:

```sh
cargo +1.91.1 run --offline --locked --manifest-path ipnet/2.12.2/verification/bugs/heapless-feature-repro/Cargo.toml --features heapless
cargo +1.91.1 run --offline --locked --manifest-path ipnet/2.12.2/verification/bugs/heapless-feature-repro/Cargo.toml --features legacy
```

Observed output:

```text
heapless=true legacy=false bytes=18 allocations=3
heapless=false legacy=true bytes=18 allocations=0
```

The exact allocation count may depend on toolchain/allocator details; the
assertion checks positive allocation for heapless-only and zero for legacy.
The same Cargo.lock pins both cases (serde 1.0.229, heapless 0.9.2). The root
crate source, manifest and lockfile are unchanged. This isolated package is
not formal proof evidence and cannot be published (`publish=false`).

Suggested future fix: select the stack-buffer path for either heapless or
ser_as_str, or deliberately make heapless enable the legacy branch with an
appropriate compatibility policy. Preserve the distinction that ser_as_str
alone does not enable serde. Add a regression serializer that distinguishes
collect_str's default allocation from stack-buffer serialize_str. No upstream
source change, issue, PR or publication has been made.


## IPv6 extension (2026-10-16)

The independent `src/bin/ipv6.rs` executable now directly confirms the same
known cfg defect for `ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/128` (43 bytes).
The exact-output sink allocates nothing; counters are reset after parsing.
Heapless-only has 4 allocations/reallocations; legacy has zero. This extends
IPNET-003 to IPv6 rather than claiming a new bug or a formal serialization proof.
Run the same commands above with `--bin ipv6`; `default-run` preserves the
original IPv4 command. See ipv6-heapless.log, ipv6-legacy.log and
ipv6-evidence.json for this separate run and exact artifact hashes. Original
IPv4 logs/evidence are preserved as historical records.

## Isolated correction candidate

A local four-guard cfg correction and its source provenance are retained in
[heapless-candidate](../../heapless-candidate/README.md) for a future upstream PR.
[Partial results](../../heapless-candidate/results.md) record 10 native feature
combinations, conditional capacity proofs, explicit external assumptions and the
remaining Aeneas mutable formatter boundary. The original release is unchanged;
no PR or publication has been made.
