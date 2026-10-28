# Standard CLI layout validation — 2026-10-28

This validation covers the local migration to tracked release sources and direct
Lean builds on macOS arm64. It is separate from the historical extraction acceptance
in results.md. Rust-to-Lean extraction was not rerun.

- All 18 release files in upstream/ match source.lock.json, including executable bits.
- Aeneas base 8e62dc3dc765602833c86b68dceb18a475a50a8f plus the existing patch restores tree 818b384f6f3d2c82f3d39a2205d3f443add1fc84.
- Charon base 08d7c9d50144bd84848212c24701253585e90d1f plus the existing patch restores tree 8bc8af4729f6833de500e607b24dfd68847ca316.
- Both the working tree and a separate checkout without an existing .work build successfully. Fixed dependency compilation caches were reused; maintained proof modules were built afresh.
- The full audit passes for 625 theorem roots, with mapping metadata checked and equal before/after input fingerprints. Allowed foundational axioms are propext, Classical.choice and Quot.sound.
- The real CLI integration test resolves all 160 mappings, records patched Charon as not_run, and confirms tool source and fingerprint stability. The mappings cover 151 distinct public API paths.
- Native default, no-default-features and all-features tests pass separately. Reviewed standard-library source hashes, Aeneas/Charon compatibility and checked shift examples pass. The pinned runtime-check configuration and all maintained Lean sources remain unchanged.
- CLI tests: 72 pass, four opt-in tests skipped; the new real integration test was also explicitly run and passed. Common Python tests: 106 pass, one skip. Service suite: 238 pass, two skips; the additional Charon-only adapter test also passes. Type checking and packaged preview consistency pass.

The standard recording command reaches the existing “Push the source commit before
cargo proofs run” condition. This migration has no new SARIF recording, push,
publication, deployment, Linux acceptance or fresh extraction claim. Publishing also
requires server support for patched Charon and registration of the pinned Aeneas base.

Detailed logs, observed tool provenance and the receipt remain local under
.work/standard-cli-migration/. Historical .work directories and unrelated untracked
files were preserved. The upstream snapshot retains original whitespace and ignore
rules; its Cargo.lock is included explicitly despite the upstream ignore rule.
