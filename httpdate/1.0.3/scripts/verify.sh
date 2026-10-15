#!/usr/bin/env bash
set -euo pipefail
version_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
repo_dir=$(cd -- "$version_dir/../.." && pwd)
cd "$version_dir"
source "$repo_dir/scripts/activate.sh"
# Invoke Why3find directly: cargo-creusot overrides WHY3CONFIG.
export WHY3CONFIG="$version_dir/scripts/why3.conf"
export DUNE_DIR_LOCATIONS="why3find:lib:$XDG_DATA_HOME/creusot/share/why3find"
creusot_version=$(cargo creusot version)
if [[ ${creusot_version%%$'\n'*} != 'cargo-creusot 0.13.0' ]]; then
  echo 'Creusot 0.13.0 is required; run scripts/setup-cloud.sh.' >&2
  exit 1
fi
# cargo-creusot 0.13 searches proof patterns only beneath verif/.
mkdir -p verif
run_dir=$(mktemp -d verif/httpdate-run-XXXXXXXX)
printf 'Run artifacts: %s\n' "$run_dir"
python3 scripts/check-proofs.py --snapshot > "$run_dir/inputs.json"
printf '%s\n' "$creusot_version" > "$run_dir/versions.txt"
cargo proofs --version >> "$run_dir/versions.txt"
rustc -Vv >> "$run_dir/versions.txt"
rustc +nightly-2026-06-22 -Vv >> "$run_dir/versions.txt"
why3 --version >> "$run_dir/versions.txt"
why3find --version >> "$run_dir/versions.txt"
alt-ergo --version >> "$run_dir/versions.txt"
z3 --version >> "$run_dir/versions.txt"
cvc4 --version >> "$run_dir/versions.txt"
cvc5 --version >> "$run_dir/versions.txt"
cargo test --locked --release -p httpdate 2>&1 | tee "$run_dir/tests.log"
# Creusot's output directory is not tracked by Cargo's build cache.
# Rebuild only this package so each run actually generates fresh Coma files.
cargo +nightly-2026-06-22 clean --target-dir target/creusot -p httpdate
cargo creusot --only=coma --span-mode off --output-dir "$version_dir/$run_dir/coma" -- --locked 2>&1 | tee "$run_dir/compile.log"
# Use the fingerprinted local timeout configuration without changing VCs.
mapfile -t targets < <(python3 scripts/check-proofs.py --targets)
test "${#targets[@]}" -gt 0
files=()
for target in "${targets[@]}"; do
  file="$run_dir/coma/verif/httpdate_rlib/$target.coma"
  test -s "$file"
  files+=("$file")
done
why3find prove --no-cache --summary --no-autodetect-provers --prover=-cvc4 -j 2 --fast 1 --time 10 -d 2 "${files[@]}" 2>&1 | tee "$run_dir/prove.log"
mapfile -t open_targets < <(python3 scripts/check-proofs.py --open-targets)
open_files=()
for target in "${open_targets[@]}"; do
  file="$run_dir/coma/verif/httpdate_rlib/$target.coma"
  test -s "$file"
  open_files+=("$file")
done
# Capture the known incompatibility without treating it as a successful proof.
set +e
why3find prove --no-cache --summary --no-autodetect-provers --prover=-cvc4,-cvc5 -j 2 -d 2 "${open_files[@]}" 2>&1 | tee "$run_dir/open-prove.log"
open_status=${PIPESTATUS[0]}
set -e
printf '%s\n' "$open_status" > "$run_dir/open-prove.exit"
python3 scripts/check-proofs.py "$run_dir"
