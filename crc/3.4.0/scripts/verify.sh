#!/usr/bin/env bash
set -euo pipefail
CRC_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
exec python3 "$CRC_ROOT/../../scripts/aeneas-manage.py" verify "$CRC_ROOT" "$@"
