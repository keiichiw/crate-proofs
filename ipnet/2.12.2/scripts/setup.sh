#!/usr/bin/env bash
set -euo pipefail
CRATE_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
exec python3 "$CRATE_ROOT/../../scripts/aeneas-manage.py" setup "$CRATE_ROOT" "$@"
