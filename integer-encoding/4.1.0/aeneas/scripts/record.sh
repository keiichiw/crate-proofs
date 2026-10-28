#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export RUSTUP_TOOLCHAIN=1.91.1
export ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0
CLI="${CARGO_PROOFS_BIN:-cargo-proofs}"
cd "$ROOT/aeneas/profiles/default/proofs"
lake build
exec "$CLI" proofs run --manifest-path "$ROOT/Cargo.toml" --proofs-config aeneas/profiles/default/proofs.toml -- lake build
