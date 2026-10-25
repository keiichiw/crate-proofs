#!/usr/bin/env bash
set -euo pipefail
EVIDENCE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERSION_ROOT="$(cd "$EVIDENCE_DIR/../../../.." && pwd)"
SESSION="$VERSION_ROOT/.work/report-findings-preview"
RECORDED_SESSION="$VERSION_ROOT/.work/preview-session"
SOURCE="$RECORDED_SESSION/source/bytes/1.12.1"
source "$SOURCE/scripts/env.sh"
export PATH="$SESSION/bin:${RUSTUP_HOME:-$HOME/.rustup}/toolchains/1.91.1-aarch64-apple-darwin/bin:$PATH"
export PROOFS_RECORD_DIR="$SESSION/records"
export AENEAS_TOOL_CACHE="$VERSION_ROOT/../../.work/tools"
export AENEAS_ARCHIVE_CACHE="$VERSION_ROOT/.work/cache"
export AENEAS_LAKE_CACHE="$VERSION_ROOT/.work/selected-proofs/.lake/packages"
cd "$SOURCE/.work/selected-proofs"
exec cargo proofs preview --manifest-path "$SOURCE/Cargo.toml" \
  --proofs-config .work/report-findings.toml \
  --api-aliases "$EVIDENCE_DIR/../api-aliases.json" \
  --run 29ae1f77-352a-486c-a5ce-4818ca5d2a72 --no-browser "$@"
