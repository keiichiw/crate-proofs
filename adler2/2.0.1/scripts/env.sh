#!/usr/bin/env bash
# Source from Bash; this environment is independent of the Creusot activation.
ADLER_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export ADLER_ROOT
export PATH="$ADLER_ROOT/.tools/cargo-proofs/bin:$ADLER_ROOT/.tools/aeneas/bin:$ADLER_ROOT/.tools/aeneas/charon/bin:$PATH"
export RUSTUP_TOOLCHAIN=1.91.1
