#!/usr/bin/env bash
set -euo pipefail
CRC_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
profile="${1:-default}"
case "$profile" in default|stage2) ;; *) echo 'profile must be default or stage2' >&2; exit 2 ;; esac
if [[ $# -gt 0 ]]; then shift; fi
bash "$CRC_ROOT/scripts/setup.sh" --profile "$profile"
source "$CRC_ROOT/scripts/env.sh"
export AENEAS_TOOL_CACHE="${AENEAS_TOOL_CACHE:-$(cd "$CRC_ROOT/../.." && pwd)/.work/tools}"
export AENEAS_ARCHIVE_CACHE="${AENEAS_ARCHIVE_CACHE:-$CRC_ROOT/.work/cache}"
export AENEAS_LAKE_CACHE="${AENEAS_LAKE_CACHE:-$CRC_ROOT/.work/selected-proofs/.lake/packages}"
cd "$CRC_ROOT/.work/selected-proofs"
exec cargo proofs run --manifest-path "$CRC_ROOT/Cargo.toml" --proofs-config "aeneas/profiles/$profile/proofs.toml" -- lake build "$@"
