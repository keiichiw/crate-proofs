#!/usr/bin/env bash
set -euo pipefail
SESSION=/Users/keiichiw/workspace/crate-proofs/bytes/1.12.1/.work/preview-session
ROOT="$SESSION/source/bytes/1.12.1"
source "$ROOT/scripts/env.sh"
export PATH="$SESSION/bin:$PATH"
export AENEAS_TOOL_CACHE=/Users/keiichiw/workspace/crate-proofs/.work/tools
export AENEAS_ARCHIVE_CACHE=/Users/keiichiw/workspace/crate-proofs/bytes/1.12.1/.work/cache
export AENEAS_LAKE_CACHE=/Users/keiichiw/workspace/crate-proofs/bytes/1.12.1/.work/selected-proofs/.lake/packages
export CARGO_NET_OFFLINE=true
export PROOFS_RECORD_DIR="$SESSION/records"
cd "$ROOT/.work/selected-proofs"
cargo proofs run --local --manifest-path "$ROOT/Cargo.toml" --proofs-config aeneas/profiles/default/proofs.toml --api-aliases /Users/keiichiw/workspace/crate-proofs/bytes/1.12.1/verification/preview/2026-10-23/api-aliases.json -- lake build
