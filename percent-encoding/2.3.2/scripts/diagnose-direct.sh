#!/usr/bin/env bash
set -euo pipefail
version_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
repo_dir=$(cd -- "$version_dir/../.." && pwd)
source "$repo_dir/scripts/activate.sh"
exec python3 "$version_dir/scripts/diagnose-direct.py" "$@"
