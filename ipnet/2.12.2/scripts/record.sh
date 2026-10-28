#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
bash "$ROOT/scripts/setup.sh"
source "$ROOT/scripts/env.sh"
export AENEAS_TOOL_CACHE="${AENEAS_TOOL_CACHE:-$(cd "$ROOT/../.." && pwd)/.work/tools}"
export AENEAS_ARCHIVE_CACHE="${AENEAS_ARCHIVE_CACHE:-$ROOT/.work/cache}"
cd "$ROOT/.work/selected-proofs"
exec cargo proofs run --manifest-path "$ROOT/Cargo.toml" --proofs-config aeneas/profiles/default/proofs.toml -- lake build
