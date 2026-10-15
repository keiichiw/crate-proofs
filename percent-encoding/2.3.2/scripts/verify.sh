#!/usr/bin/env bash
set -euo pipefail
version_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
repo_dir=$(cd -- "$version_dir/../.." && pwd)
cd "$version_dir"
source "$repo_dir/scripts/activate.sh"
if (($#)); then echo "usage: $0" >&2; exit 2; fi

mkdir -p "$version_dir/verif"
run_dir=$(mktemp -d "$version_dir/verif/percent-encoding-XXXXXXXX")
mkdir -p "$run_dir/coma" "$run_dir/target"
printf 'Fresh proof attempt: %s\n' "$run_dir"

dependency_dir="$repo_dir/form_urlencoded/1.2.2"
python3 "$dependency_dir/scripts/audit-direct-evidence.py" "$dependency_dir" \
  --manifest "$dependency_dir/verification/evidence/direct-s8YxnYN7/manifest.json" \
  >"$run_dir/dependency-audit.json"
python3 scripts/check-proofs.py --snapshot "$run_dir/inputs-before.json"
(cd "$version_dir/crate" && cargo metadata --offline --locked --format-version 1) \
  >"$run_dir/cargo-metadata.json"
differential_dir="$version_dir/verification/differential"
native_differential_log="$differential_dir/differential-run-full-scope.log"
native_run_id=$(sed -n '1s/^RUN_ID=//p' "$native_differential_log")
[[ "$native_run_id" == percent-encoding-2.3.2-full-scope-* \
   && "$native_run_id" != percent-encoding-2.3.2-full-scope- ]] || {
  echo "missing/invalid unique full-scope native run ID" >&2; exit 1;
}
native_logs=(
  differential-run-full-scope.log
  fork-unit-all-features-full-scope.log
  fork-doc-all-features-full-scope.log
  fork-check-default-full-scope.log
  fork-check-bare-full-scope.log
  fork-check-alloc-full-scope.log
  upstream-unit-all-features-full-scope.log
)
mkdir -p "$run_dir/native-evidence"
for name in "${native_logs[@]}"; do
  source_log="$differential_dir/$name"
  [[ -f "$source_log" ]] || { echo "missing full-scope native log: $source_log" >&2; exit 1; }
  rg -q "^RUN_ID=${native_run_id}$" "$source_log" || {
    echo "native log has wrong/missing run ID: $source_log" >&2; exit 1;
  }
  cp "$source_log" "$run_dir/native-evidence/$name"
done
python3 - "$run_dir/native-evidence/differential-run-full-scope.log" <<'PY'
import json, sys
lines = open(sys.argv[1], encoding="utf-8").read().splitlines()
records = [json.loads(line) for line in lines if line.startswith("{")]
run_id = lines[0].removeprefix("RUN_ID=") if lines else ""
if not run_id.startswith("percent-encoding-2.3.2-full-scope-") \
        or len(records) != 1 or records[0].get("run_id") != run_id \
        or records[0].get("status") != "passed":
    raise SystemExit("full-scope native differential summary missing, duplicated, or failed")
PY
cp "$run_dir/native-evidence/differential-run-full-scope.log" "$run_dir/differential.log"
cp "$differential_dir/source-fingerprint-full-scope.txt" "$run_dir/native-evidence/source-fingerprint.txt"
grep -qx "RUN_ID=${native_run_id}" "$run_dir/native-evidence/source-fingerprint.txt" || {
  echo "native source fingerprint has wrong/missing run ID" >&2; exit 1;
}
# Native checks must use the same source/harness bytes before and after execution.
python3 scripts/check-native-fingerprint.py \
  --fingerprint "$run_dir/native-evidence/source-fingerprint.txt" \
  --snapshot "$run_dir/inputs-before.json" \
  --repo-root "$repo_dir" --version-dir "$version_dir" --run-id "$native_run_id"
# A unique target directory and --offline keep this compile isolated and socket-free.
(cd "$version_dir/crate" && cargo creusot --only=coma --span-mode off \
  --output-dir "$run_dir/coma" -- --locked --offline --target-dir "$run_dir/target") \
  >"$run_dir/compile.log" 2>&1

python3 scripts/prove-direct.py --generated-dir "$run_dir/coma/verif/percent_encoding_rlib" \
  --run-dir "$run_dir" --output "$run_dir/bundle"
python3 scripts/audit-direct-evidence.py "$version_dir" --manifest "$run_dir/bundle/manifest.json"

evidence_dir="$version_dir/verification/evidence"
mkdir -p "$evidence_dir"
run_name=$(basename "$run_dir")
cp -a "$run_dir/bundle" "$evidence_dir/$run_name"
python3 scripts/audit-direct-evidence.py "$version_dir" \
  --manifest "$evidence_dir/$run_name/manifest.json" >"$evidence_dir/$run_name/archive-audit.json"
ln -s "$run_name" "$evidence_dir/latest.next"
python3 - "$evidence_dir/latest.next" "$evidence_dir/latest" <<'PYLINK'
import os, sys
os.replace(sys.argv[1], sys.argv[2])
PYLINK
printf 'Evidence bundle: %s/verification/evidence/latest/manifest.json\n' "$version_dir"
