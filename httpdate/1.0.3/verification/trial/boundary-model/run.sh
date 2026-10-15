#!/usr/bin/env bash
set -euo pipefail
model_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
version_dir=$(cd -- "$model_dir/../../.." && pwd)
repo_dir=$(cd -- "$version_dir/../.." && pwd)
cd "$model_dir"
source "$repo_dir/scripts/activate.sh"
test "$(uname -s)" = Linux
test "$(getconf LONG_BIT)" = 64
mkdir -p verif
run_dir=$(mktemp -d verif/boundary-run-XXXXXXXX)
printf 'Conditional-model artifacts: %s\n' "$run_dir"
python3 check.py --snapshot > "$run_dir/inputs.json"
cargo creusot version > "$run_dir/versions.txt"
cargo proofs --version >> "$run_dir/versions.txt"
rustc -Vv >> "$run_dir/versions.txt"
rustc +nightly-2026-06-22 -Vv >> "$run_dir/versions.txt"
cargo test --locked 2>&1 | tee "$run_dir/tests.log"
cargo +nightly-2026-06-22 clean --target-dir target/creusot -p httpdate-boundary-model
cargo creusot --only=coma --span-mode off --output-dir "$model_dir/$run_dir/coma" -- --locked 2>&1 | tee "$run_dir/compile.log"
targets=(bounded_epoch_seconds epoch_time time_boundary_roundtrip ascii_text normalized_ascii)
files=()
for target in "${targets[@]}"; do
  file="$run_dir/coma/verif/httpdate_boundary_model_rlib/$target.coma"
  test -s "$file"
  files+=("$file")
done
cargo creusot --only=prove --no-cache --why3find-arg=-d --why3find-arg=2 "${files[@]}" 2>&1 | tee "$run_dir/prove.log"
python3 check.py "$run_dir"
