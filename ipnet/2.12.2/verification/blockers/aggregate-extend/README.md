# Narrow Vec::extend extraction boundary

These are read-only probes of both family aggregate methods against the pinned
Aeneas/Charon toolchain. They do not enter `proofs/Ipnet.lean`,
`verification/aeneas.json`, or audited API coverage. From the crate directory,
regenerate all four diagnostics in fresh ignored output directories and package
their logs here:

```bash
python3 verification/blockers/aggregate-extend/refresh.py
```

All four official helper runs reject the incomplete generated model. Config 01
adds the exact IPv4 aggregate entry and `alloc::vec::_::extend`: its body calls
opaque `SpecExtend::spec_extend`. Config 02 selects that method too, revealing
opaque `Vec::extend_desugared`. Config 03 selects the latter and extracts its
iterator loop, which calls opaque `Vec::capacity`, `reserve`, `as_mut_ptr`,
`set_len`, `core::ptr::write`, and raw-pointer addition. These allocation and
write effects are outside the audited Vec model. The checked subnet trace
establishes input iteration, but not the missing vector mutation relation.

Config 04 repeats the third stage with `Ipv6Net::aggregate`. It reaches the
same `Vec::extend_desugared` and raw-pointer dependencies, so the boundary is
observed directly for both address families. The `01-*` through `04-*` files
are the latest rejected generated Lean text and extraction logs, not admitted
models or aggregate proofs. `evidence.json` records current SHA-256 values and
the active extractor patch/binary hashes. The preceding research snapshots are
preserved only under ignored `verification/runs/historical-aggregate-extend/`,
excluded from commit.

This does not show that ipnet's aggregation is incorrect. Sorting,
`last_mut` backward update, and collection contracts described in
`verification/ipv4-aggregate-boundaries.md` also remain open.
