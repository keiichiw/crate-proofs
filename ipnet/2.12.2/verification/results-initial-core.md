# Local verification results — ipnet 2.12.2

Accepted run: **2026-10-16**, [check-SADOiIZ0](runs/check-SADOiIZ0/result.json).
The full version-local verifier passed. This is a **15-API constructor/observer
core**, not verification of the whole crate or the entire initial specification.

## Formal coverage

For each of `Ipv4Net`, `Ipv6Net`, and `IpNet`, the actual extracted bodies of
`new`, `new_assert`, `addr`, `prefix_len`, and `max_prefix_len` have audited
Lean total-success contracts (15 theorems / 15 public API mappings).

- `new` covers every `u8` prefix: an exact Rust `Ok` network for a valid width,
  otherwise exactly `Err(PrefixLenError)`, with outer Aeneas success in both cases.
- Constructors preserve the full original address, including host bits. `IpNet`
  covers both tags without conflating IPv4 and IPv6.
- `new_assert` proves total success for prefixes ≤32 or ≤128 as appropriate.
  Invalid-prefix panic behavior is outside these contracts.
- Observers return the exact stored address/prefix or address-family maximum.
  Their proofs even apply to arbitrary generated structures, without an alignment
  or valid-prefix precondition.

Astra independently derived and reviewed the [specification](specification.md).
Sol completed the implementation proofs in `proofs/Proofs/Core.lean`; Astra also
served as the extraction oracle. The primary reviewed statements, mappings,
provenance, commands and coverage and executed the complete verifier.
[theorems.json](theorems.json) and [proofs.toml](../proofs.toml) enumerate the
accepted names and exact preconditions. Generated `From<Ipv4Net>` and
`From<Ipv6Net>` dependency bodies do not have standalone public API contracts.

## Checks performed

- Registry archive SHA-256, captured source inventory, embedded release commit,
  clean upstream submodule, Gitlink, all tracked source bytes and Cargo build surface.
- Exact tool/dependency revisions, tool binary hashes and the recorded compatibility patch.
- Fresh shared extraction; every generated Lean file byte-identical to its maintained copy.
- `lake clean ipnet-proofs`, rebuild, and transitive theorem-kind/axiom audit: **15/15 passed**.
  Only `propext`, `Classical.choice`, and `Quot.sound` are permitted; no `sorryAx`,
  application axioms or native-decision axioms were accepted.
- Before/after fingerprints match, including all specification/proof inputs and the
  shared extraction/audit scripts.
- Separate native tests: default features **33 unit + 56 doc tests passed**;
  `--no-default-features` **33 unit + 56 doc tests passed**. These finite tests
  do not extend formal coverage, and the formal extraction uses default features.

## Source and tools

The official registry index selected 2.12.2 as latest non-yanked stable release
on 2026-10-16; published 2026-09-06. Registry archive checksum:
`791930b43c0d5973160d90a8f3894509f2b273430f5c5c73b668636d0287c5c0`.
Upstream commit: `13c5c5873c02127679b1e8e64b538e4e36942640`.

Aeneas `8e62dc3dc765602833c86b68dceb18a475a50a8f`, compatible Charon
`08d7c9d50144bd84848212c24701253585e90d1f`, proofs-rs
`a2335432635301597f203e1159e3d16888ce2333` (cargo-proofs 0.4.1), extraction Rust
`nightly-2026-09-17`, native Rust `1.91.1`, Lean `4.35.0`, macOS arm64.
See [toolchain.json](toolchain.json) for binary identities and the exact
proofs-rs audit-identifier compatibility patch. Aeneas and proofs-rs HEAD were
resolved afresh; the prior adler2 target was not treated as today's latest pin.

## Unproved scope and trust

`netmask`, `hostmask`, `network`, `broadcast`, and `trunc` remain unproved.
Narrow arithmetic extraction reaches unsupported standard-library
`unchecked_shl` → `ub_checks` / panic dependencies. Broad extraction also reaches
unrelated alignment enum discriminants that overflow the extractor's OCaml integer.
Rejected experiments and exact diagnosis are recorded in
[extraction-notes.md](extraction-notes.md). No generated models were edited,
custom axioms added, or arithmetic contracts weakened to hide those boundaries.

Mask parsing/construction, containment, supernets/siblings, host/subnet/range
iterators, aggregation, parsing/formatting, other conversions and traits,
serde/schema integrations, optional features and alternative platforms have no
accepted contracts here. All independently specified extensions remain obligations.

Trust remains in Rust-to-LLBC-to-Lean translation, the selected Aeneas library
semantics, the Lean kernel, and source/tool provenance checks. Concrete standard
library address representations are extracted as byte arrays, not type axioms.
This evidence does not prove the extractor correct or establish compiler-level
Rust semantics. cargo-proofs recording/publication was not run, and no login,
push or publication occurred.

## Evidence identity and reproduction

Run `bash ipnet/2.12.2/scripts/verify.sh` from the repository root.
The accepted run is preserved locally under `verification/runs/`, ignored by Git.
The earlier `check-8jwBOyuN` stopped on a sandbox dependency-download failure;
it has no success result and was not overwritten. Fixed locked dependencies were
fetched before the accepted fresh run.

- Complete result SHA-256: `913af646d342ede82787ed85c25ea237568d718811cca108d58e3fe18f7060f6`
- Input fingerprint SHA-256: `c70e65355d937feb0cb895df419251e90987fc335ea0e003fa729a9913a3eed8`
- Audit result SHA-256: `a6474bfb7055db9744672868624e5e6fe9d0aa87c29023736bd5316773f609d0`

The result JSON records individual artifact/log hashes. This results document is
a post-run summary and is intentionally outside the input fingerprint.
