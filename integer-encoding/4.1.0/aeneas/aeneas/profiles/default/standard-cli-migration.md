# Standard CLI layout validation — 2026-10-28

The Aeneas workspace was imported from develop commit
9789a80aead79a928882efba97003cb34da5422d.
This is macOS arm64 validation of the tracked-source/direct-Lean-build layout,
separate from the historical extraction acceptance in results.md.

- The complete upstream/ snapshot matches source.lock.json, including executable bits.
- The standalone Cargo workspace references that snapshot directly. Lake uses official Aeneas be86ab0f1989d04944292b345b24c435be3ad10a; neither Aeneas nor Charon has a patch.
- A separate checkout without .work builds the maintained Lean proofs successfully. Fixed dependency caches were reused; local proof modules were built afresh.
- All 163 roots across 11 modules pass the dependency/axiom audit. Before/after input fingerprints match. Only propext, Classical.choice and Quot.sound are allowed.
- All 80 mappings resolve through the real CLI, in both the working tree and separate checkout. Their public trait paths are fully qualified; theorem names, modules and preconditions are unchanged. The remaining ten scalar decode candidates remain outside formal coverage.
- Report prose and all 23 maintained Lean files are unchanged from develop.
- Native debug/release harnesses pass 15 tests each, upstream tests pass 31, and the documentation example passes. These are finite observations for the default feature configuration, including 130 builtin instances and separate generic/error/consumption cases; they are not formal or async coverage.
- Selected standard-library hashes/excerpts and the direct FixedInt model whitelist pass. Inventory and coverage checks pass.
- Common Python suite: 106 pass, one skip. CLI suite: 72 pass, five opt-in tests skipped. The real integer-encoding integration and ipnet's 160-mapping integration were explicitly run and passed. The expanded-API regression covers inherited defaults, explicit overrides, private traits and unknown external defaults.

The CLI now enumerates inherited defaults only from active traits defined in the
selected crate when expand_api is enabled. API enumeration is not proof evidence.

An initial concurrent build failed while shared dependency setup metadata was
being written. Builds were serialized afterward; the separate checkout build and
final full audit succeeded. The final receipt is authoritative for this migration.

Rust-to-Lean generation was not rerun. No new SARIF recording, Linux acceptance,
commit, push, publication or deployment is claimed. The standard recording command
reaches the existing requirement to commit and push source changes first. Existing
setup/verify remain the separate extraction workflow; historical evidence is not a
prerequisite for the standard build. Full local logs and receipt are retained under
.work/standard-cli-migration/.
