#!/usr/bin/env bash
set -euo pipefail
CRC_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
profile="${1:-default}"
case "$profile" in default|stage2) ;; *) echo 'profile must be default or stage2' >&2; exit 2 ;; esac
if [[ $# -gt 0 ]]; then shift; fi
source "$CRC_ROOT/scripts/env.sh"
cd "$CRC_ROOT/aeneas/profiles/$profile/proofs"
exec cargo proofs run --manifest-path "$CRC_ROOT/Cargo.toml" --proofs-config "aeneas/profiles/$profile/proofs.toml" -- lake build "$@"
