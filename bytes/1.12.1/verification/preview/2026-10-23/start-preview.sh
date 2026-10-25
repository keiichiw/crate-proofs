#!/usr/bin/env bash
set -euo pipefail
EVIDENCE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERSION_ROOT="$(cd "$EVIDENCE_DIR/../../.." && pwd)"
SESSION="$VERSION_ROOT/.work/preview-session"
SOURCE="$SESSION/source/bytes/1.12.1"
source "$SOURCE/scripts/env.sh"
export PATH="$SESSION/preview-bin:$PATH"
export PROOFS_RECORD_DIR="$SESSION/records"
export AENEAS_TOOL_CACHE="$VERSION_ROOT/../../.work/tools"
export AENEAS_ARCHIVE_CACHE="$VERSION_ROOT/.work/cache"
export AENEAS_LAKE_CACHE="$VERSION_ROOT/.work/selected-proofs/.lake/packages"
cd "$SOURCE/.work/selected-proofs"
exec cargo proofs preview --manifest-path "$SOURCE/Cargo.toml" \
  --proofs-config aeneas/profiles/default/proofs.toml \
  --api-aliases "$EVIDENCE_DIR/api-aliases.json" \
  --findings "$EVIDENCE_DIR/findings.json" --no-browser "$@"
