# Local verification results — ipnet 2.12.2

Accepted run: **2026-10-16**, [check-16X2Z9mu](runs/check-16X2Z9mu/result.json).
The complete verifier passed with **283 audited theorems: 66 public contracts
and 217 helpers**. All 243 previous theorem identities remain. This checkpoint
adds 40 helpers and no public API contract. Previous API coverage and its detailed
conditions are preserved in [results-ipv4-core.md](results-ipv4-core.md).

## New confirmed bug and stopping condition

**IPNET-003: the documented heapless feature does not select allocation-avoiding
human-readable serialization.** Actual IPv4 serialization selects its stack buffer
only under the legacy ser_as_str feature. With an allocation-free serialize_str
sink inheriting serde's default collect_str, heapless alone performs three
allocation/reallocation calls; legacy serde + ser_as_str performs zero. Both
produce exactly `255.255.255.255/32`. Exact counts are environment-dependent;
the regression is that the documented new feature fails to select the intended
branch. IPv6 has the same source guard; the executable reproduction tests IPv4.

Astra identified and reproduced the issue, and the primary independently reran
both locked offline configurations. See [reproduction and future fix direction](bugs/heapless-feature-repro/README.md)
and [bug ledger](bugs/README.md). Source, lockfile, logs and hashes are saved.
This is native evidence, not a Lean theorem. It is a new bug, distinct from the
previous schema findings and already-known raw subnet q>32 panic domain.
The user's requested stopping condition is met, so proof expansion stopped at
this checked checkpoint. No upstream source edits, issue, PR or publication.

## Checked subnet helpers and precise remaining scope

Astra independently specified/reviewed and Sol proved four helper modules:

- IPv4SubnetMath: greatest admissible block height, alignment, fitting,
  canonicality, exact interval partition and strictly decreasing remainder.
- IPv4SubnetBits: exact relation from the existing Nat-log leading-zero model
  to core BitVec.clz/ctz, and trailing-zero counts to divisibility by powers of two.
- IPv4SubnetRangeBits: leading-zero bounds, complemented remainders,
  trailing-ones/Mersenne equivalence and a pure range-threshold lemma.
- IPv4SubnetStep: constructor state and actual extracted next on empty ranges,
  for every U8 minimum prefix, with unchanged state; actual trailing_ones helper.

The pure threshold assumptions still need to be discharged for actual counts.
**Nonempty next_ipv4_subnet/Ipv4Subnets::next, finite enumeration, fixed-prefix
composition and aggregate are not proved.** Selected unproved bodies are explicitly
listed in the inventory. Parsing/formatting, other unmapped traits, optional
integrations and generic consumers remain open; see the [coverage ledger](ipv4-coverage.md)
and [remaining API inventory](ipv4-remaining-coverage.md).
The empty-state helper is not presented as a full next API contract.

## Trust and reproducible evidence

All earlier model, translation and platform restrictions remain as documented
in the [previous result](results-ipv4-core.md) and [model ledger](model-boundaries.md).
The new narrow standard-library model is U32.trailing_zeros, returning normal
success with the reverse-bit leading-zero count. Astra reviewed correspondence
to pinned Rust cttz including zero and MAX. That Rust/model correspondence is
trusted; the divisibility consequences are kernel-checked. Actual Rust
trailing_ones is extracted, not separately replaced. No ipnet algorithm was
replaced with a desired specification. Aggregate extraction probes are not claims.

- Unchanged release source/Gitlink, tool identities and exact patched dependency
  checks passed before and after verification.
- Fresh extraction byte-matched all maintained generated Lean files.
- Local Lake clean/rebuild and all 283 transitive theorem/mapping audits passed;
  only propext, Classical.choice and Quot.sound are allowed.
- Public mappings remain 66, including existing explicit 64-bit restrictions
  for Usize-sensitive range methods; no whole-crate claim.
- Eight kernel shift examples passed.
- Native default and no-default-features each passed **33 unit + 17 integration
  + 56 doc tests**. New finite subnet and aggregate tests check independent
  CIDR/union observations; they do not prove universal correctness.
- Input fingerprints before/after match. The primary independently checked all
  recorded artifact hashes, the current fingerprint and bug reproduction hashes.

Current combined Aeneas patch SHA-256:
8589655e2d39572d71603e8d9591c8ad47472df415a17e73961b15bcad6eeb1e.

Reproduce with `bash ipnet/2.12.2/scripts/verify.sh` from repository root.
Evidence remains local in the ignored run directory. This report is excluded
from the input fingerprint.

- Complete result SHA-256: d7183473cf59c3dc0d55ef3b90091669be3a3aa3a7e5a6c1cc0641341fba3582
- Input fingerprint SHA-256: 25230343500f6fc27463016d2fae30162b30c17e5f02a95935c06a9636a21bd6
- Audit result SHA-256: 297f16b26d1ab53c9abe2b924c09142c22559c17f4a7663fa983bae1bb64329a
