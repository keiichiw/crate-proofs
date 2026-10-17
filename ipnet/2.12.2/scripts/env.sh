#!/usr/bin/env bash
IPNET_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export IPNET_ROOT
# macOS login Bash can omit Homebrew, leaving Python 3.9 without tomllib.
if ! python3 -c 'import tomllib' >/dev/null 2>&1; then
  if [[ -x /opt/homebrew/bin/python3 ]]; then
    export PATH="/opt/homebrew/bin:$PATH"
  fi
fi
python3 -c 'import tomllib' || { printf '%s\n' 'Python >=3.11 is required.' >&2; return 1; }
export PATH="$IPNET_ROOT/.tools/cargo-proofs/bin:$IPNET_ROOT/.tools/aeneas/bin:$IPNET_ROOT/.tools/aeneas/charon/bin:$PATH"
export RUSTUP_TOOLCHAIN=1.91.1
