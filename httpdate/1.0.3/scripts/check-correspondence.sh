#!/usr/bin/env bash
set -euo pipefail
version_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$version_dir"
mkdir -p verif
run_dir=$(mktemp -d "$version_dir/verif/correspondence-XXXXXXXX")
python3 - "$@" > "$run_dir/release-check-arguments.json" <<'PY'
import json, sys
print(json.dumps(sys.argv[1:]))
PY
python3 scripts/capture-correspondence.py --snapshot > "$run_dir/inputs.json"
python3 scripts/check-upstream-release.py "$@" | tee "$run_dir/release-check.log"
cargo run --manifest-path verification/correspondence/Cargo.toml --locked --release \
  > "$run_dir/result.json" 2> "$run_dir/build.log"
cat "$run_dir/result.json"
python3 scripts/capture-correspondence.py "$run_dir"
printf 'To bind after formal verification: python3 %q --bind %q\n' "$version_dir/scripts/capture-correspondence.py" "$run_dir"
