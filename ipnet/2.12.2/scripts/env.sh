#!/usr/bin/env bash
# Source after setup; no global toolchain activation or user-home overrides.
IPNET_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export IPNET_ROOT
export PATH="$IPNET_ROOT/.work/selected-tools/cargo-proofs/bin:$IPNET_ROOT/.work/selected-tools/aeneas/bin:$IPNET_ROOT/.work/selected-tools/aeneas/charon/bin:$PATH"
export RUSTUP_TOOLCHAIN=1.91.1
export ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0
export CARGO_TARGET_DIR="$IPNET_ROOT/.work/build/native"
