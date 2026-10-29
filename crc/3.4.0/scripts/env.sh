#!/usr/bin/env bash
CRC_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export CRC_ROOT
export PATH="$CRC_ROOT/.work/selected-tools/cargo-proofs/bin:$CRC_ROOT/.work/selected-tools/aeneas/bin:$CRC_ROOT/.work/selected-tools/aeneas/charon/bin:$PATH"
export RUSTUP_TOOLCHAIN=1.91.1
export ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0
export CARGO_TARGET_DIR="$CRC_ROOT/.work/build/native"
