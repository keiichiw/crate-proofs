# integer-encoding 4.1.0 — managed Aeneas profile

```bash
bash scripts/setup.sh
bash scripts/verify.sh
bash scripts/verify.sh --offline
```

The version's independent Cargo workspace compiles immutable Git-tracked `upstream/` from
the locked release archive. Tools and exact source inventories are independently
restored; no other crate tool/source directory is needed. See the
[management guide](../../../verification/aeneas-management.md).

The [specification](aeneas/profiles/default/specification.md) preserves the original independent canonical
encoding specification, authored proofs, 80/90 builtin scalar API contracts and
explicit standard-model trust boundaries. All generated models are freshly compared
per target. External templates are never accepted as proofs; only the reviewed
FixedInt standard models are imported. Varint decoding and generic/async I/O remain
outside formal coverage. Pointer-width contracts require 64-bit targets.

Native debug/release oracle tests, upstream/doc tests and documented bug observations
remain separate from formal proof. Standard source hashes/excerpts, exact inventory,
coverage are checked against current inputs. Historical CRC bindings are not a verification input. Standard Lean build, transitive
axiom audit and before/after fingerprints complete acceptance.
[Results](aeneas/profiles/default/results.md) distinguish fresh evidence from historical
runs and unverified Linux candidates. Local verify requires no push. The optional
record wrapper retains standard CLI publication conditions; repository scripts and
preparation/native logs are excluded from SARIF. Setup/verify never publish.

Verification findings are recorded [within this version](verification/findings/README.md).

## Standard CLI recording

The release snapshot is tracked unchanged under `upstream/`. Maintained Lean
models and proofs build directly in `aeneas/profiles/default/proofs` on macOS arm64.
Lake restores the official Aeneas revision; neither Aeneas nor Charon is patched.
Setup and Rust-to-Lean extraction are not part of this recording path.

```bash
CARGO_PROOFS_BIN=/absolute/path/to/cargo-proofs bash scripts/record.sh
```

The CLI must support `tool.expand_api` to discover macro-generated scalar APIs.
The setup/verify wrappers retain the separate extraction workflow. Historical
evidence describes its original inputs and does not certify this new layout.

See [migration validation](aeneas/profiles/default/standard-cli-migration.md) for current results and scope.

### CLI revision for recording

Use [proofs-rs PR #82](https://github.com/proofs-rs/proofs-rs/pull/82), commit
`8c98569c8be379007d0649816d35de260ca43822` from
`https://github.com/keiichiw/proofs-rs.git` (branch
`codex/aeneas-charon-api-mappings`). In a checkout of that commit, build with
`cargo build --locked --manifest-path cli/Cargo.toml`, then pass the absolute
`cli/target/debug/cargo-proofs` path as `CARGO_PROOFS_BIN`.
The globally installed CLI may not contain these features.
