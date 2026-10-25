#!/usr/bin/env bash
set -euo pipefail
NUMERIC_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
source "$NUMERIC_ROOT/scripts/env.sh"
python3 "$NUMERIC_ROOT/scripts/extract-numeric.py" "$@"
