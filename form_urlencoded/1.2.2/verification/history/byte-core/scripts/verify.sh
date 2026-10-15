#!/usr/bin/env bash
set -euo pipefail
version_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
repo_dir=$(cd -- "$version_dir/../.." && pwd)
cd "$version_dir"
source "$repo_dir/scripts/activate.sh"
if [[ $# -ne 0 ]]; then
  echo "usage: $0" >&2
  exit 2
fi

mkdir -p "$version_dir/verif"
run_dir=$(mktemp -d "$version_dir/verif/form-urlencoded-XXXXXXXX")
mkdir -p "$run_dir/coma"
printf 'Fresh evidence run: %s\n' "$run_dir"

{
  cargo creusot version
  cargo-proofs --version
  rustc --version --verbose
  rustc +nightly-2026-06-22 --version --verbose
  why3 --version
  why3find --version
  alt-ergo --version || true
  z3 --version || true
  cvc4 --version || true
  cvc5 --version || true
} >"$run_dir/versions.txt" 2>&1

python3 scripts/check-proofs.py --snapshot "$run_dir/inputs-before.json"
bash scripts/run-differential.sh "$run_dir/differential"

# Ensure this run cannot silently reuse an old translated Rust artifact.
cargo +nightly-2026-06-22 clean --target-dir target/creusot -p form_urlencoded \
  >"$run_dir/clean.log" 2>&1
cargo creusot --only=coma --span-mode off --output-dir "$run_dir/coma" -- --locked --offline \
  2>&1 | tee "$run_dir/compile.log"

mapfile -t targets < <(python3 scripts/check-proofs.py --selected-files "$run_dir")
if [[ ${#targets[@]} -eq 0 ]]; then
  echo "No selected generated targets were found." >&2
  exit 1
fi
cargo creusot --only=prove --no-cache \
  --why3find-arg=-j --why3find-arg=3 --why3find-arg=-d --why3find-arg=2 \
  "${targets[@]}" 2>&1 | tee "$run_dir/prove.log"

python3 scripts/check-proofs.py --package "$run_dir"
python3 "$repo_dir/scripts/audit-proof-evidence.py" "$version_dir" \
  --manifest "$run_dir/bundle/manifest.json" \
  --source-root "$version_dir/crate/src" \
  --generated-dir "$run_dir/coma/verif/form_urlencoded_rlib" \
  --reconstruct-root-goals | tee "$run_dir/audit.log"
cp "$run_dir/audit.log" "$run_dir/bundle/audit.log"
evidence_dir="$version_dir/verification/evidence"
mkdir -p "$evidence_dir"
run_name=$(basename "$run_dir")
cp -a "$run_dir/bundle" "$evidence_dir/$run_name"
if [[ -e "$evidence_dir/latest" && ! -L "$evidence_dir/latest" ]]; then
  mv "$evidence_dir/latest" "$evidence_dir/previous-$(date -u +%Y%m%dT%H%M%SZ)"
fi
ln -s "$run_name" "$evidence_dir/latest.next"
mv -Tf "$evidence_dir/latest.next" "$evidence_dir/latest"
printf 'Evidence bundle: %s/verification/evidence/latest/manifest.json\n' "$version_dir"
