#!/usr/bin/env bash
# Source after setup; no global toolchain activation or user-home overrides.
INTEGER_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export INTEGER_ROOT
export PATH="$INTEGER_ROOT/.work/selected-tools/aeneas/bin:$INTEGER_ROOT/.work/selected-tools/aeneas/charon/bin:$PATH"
export RUSTUP_TOOLCHAIN=1.91.1
export ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0
export CARGO_TARGET_DIR="$INTEGER_ROOT/.work/build/native"
