#!/usr/bin/env bash
set -euo pipefail
version_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
repo_dir=$(cd -- "$version_dir/../.." && pwd)
cd "$version_dir"
source "$repo_dir/scripts/activate.sh"

generated_dir=""
output_dir=""
solver=z3
time_limit=30
targets=()
diagnostic=0
ground_fallback_args=()
while (($#)); do
  case "$1" in
    --generated-dir) generated_dir=$2; shift 2 ;;
    --output) output_dir=$2; shift 2 ;;
    --solver) solver=$2; shift 2 ;;
    --time-limit) time_limit=$2; shift 2 ;;
    --target) targets+=(--target "$2"); shift 2 ;;
    --diagnostic) diagnostic=1; shift ;;
    --ground-fallback) ground_fallback_args+=(--ground-fallback); shift ;;
    -h|--help)
      echo "usage: $0 [--target TARGET ...] [--solver z3|cvc5] [--time-limit SECONDS] [--output DIR]"
      echo "       $0 [--ground-fallback] [--diagnostic --generated-dir EXISTING_COMA_ROOT] [--target TARGET ...] [--output DIR]"
      exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done
if ((diagnostic)); then
  if [[ -z "$generated_dir" ]]; then echo "--generated-dir is required in --diagnostic mode" >&2; exit 2; fi
  if [[ -z "$output_dir" ]]; then output_dir=$(mktemp -d "${TMPDIR:-/tmp}/form-urlencoded-direct-XXXXXXXX"); rmdir "$output_dir"; fi
  python3 scripts/prove-direct.py --generated-dir "$generated_dir" --output "$output_dir" \
    --solver "$solver" --time-limit "$time_limit" --diagnostic \
    "${ground_fallback_args[@]}" "${targets[@]}"
  python3 scripts/audit-direct-evidence.py "$version_dir" --manifest "$output_dir/manifest.json"
  exit 0
fi
if [[ -n "$generated_dir" ]]; then echo "--generated-dir requires --diagnostic; final runs compile fresh Coma" >&2; exit 2; fi
mkdir -p "$version_dir/verif"
run_dir=$(mktemp -d "$version_dir/verif/direct-XXXXXXXX")
python3 scripts/prove-direct.py --snapshot "$run_dir/inputs-before.json"
bash scripts/run-differential.sh "$run_dir/differential"
cargo +nightly-2026-06-22 clean --target-dir target/creusot -p form_urlencoded \
  >"$run_dir/clean.log" 2>&1
cargo creusot --only=coma --span-mode off --output-dir "$run_dir/coma" -- --locked --offline \
  >"$run_dir/compile.log" 2>&1
generated_dir="$run_dir/coma/verif/form_urlencoded_rlib"
if [[ -z "$output_dir" ]]; then output_dir="$run_dir/bundle"; fi
python3 scripts/prove-direct.py --generated-dir "$generated_dir" --output "$output_dir" \
  --solver "$solver" --time-limit "$time_limit" --inputs-before "$run_dir/inputs-before.json" \
  --fresh-compile-assertion --require-complete-generated --keep-going \
  "${ground_fallback_args[@]}" "${targets[@]}"
cp "$run_dir/inputs-before.json" "$output_dir/inputs-before.json"
cp "$run_dir/compile.log" "$output_dir/compile.log"
cp "$run_dir/clean.log" "$output_dir/clean.log"
cp "$run_dir/differential/run.log" "$output_dir/differential.log"
cp "$run_dir/differential/tests.log" "$output_dir/tests.log"
cp "$run_dir/differential/check-alloc.log" "$output_dir/check-alloc.log"
python3 - "$output_dir" <<'PY'
import hashlib, json, sys
from pathlib import Path
bundle = Path(sys.argv[1])
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
log = bundle / "differential.log"
summary = None
for line in reversed(log.read_text().splitlines()):
    try: item = json.loads(line)
    except json.JSONDecodeError: continue
    if item.get("status") == "passed":
        summary = item
        break
if summary is None: raise SystemExit("native differential run has no passing summary")
expected = {"singleton_inputs": 256, "pair_inputs": 65536, "alphabet_inputs": 19608,
            "random_inputs": 129, "targeted_escape_utf8_inputs": 13}
for key, count in expected.items():
    if type(summary.get(key)) is not int or summary[key] != count:
        raise SystemExit(f"unexpected native differential {key}: {summary.get(key)!r}")
byte_total = sum(expected[key] for key in ("singleton_inputs", "pair_inputs", "alphabet_inputs", "random_inputs"))
total = byte_total + expected["targeted_escape_utf8_inputs"]
if type(summary.get("byte_input_total")) is not int or summary["byte_input_total"] != byte_total:
    raise SystemExit("native differential byte input total does not match its non-targeted case inventory")
for key in ("owned_parse_inputs", "clone_after_next_inputs"):
    if type(summary.get(key)) is not int or summary[key] != total:
        raise SystemExit(f"native differential {key} does not cover all {total} inputs")
if type(summary.get("size_hint_step_observations")) is not int or summary["size_hint_step_observations"] != 394459:
    raise SystemExit("unexpected native differential size hint observation count")
if type(summary.get("serializer_chain_cases")) is not int or summary["serializer_chain_cases"] != 1:
    raise SystemExit("unexpected native serializer chain count")
manifest_path = bundle / "manifest.json"
if not manifest_path.is_file(): manifest_path = bundle / "attempt-report.json"
manifest = json.loads(manifest_path.read_text())
manifest["native_checks_sha256"] = {name: sha(bundle / name) for name in ("tests.log", "check-alloc.log")}
manifest["native_differential"] = {"summary": summary, "log_sha256": sha(log)}
manifest["compile_log_sha256"] = sha(bundle / "compile.log")
manifest["clean_log_sha256"] = sha(bundle / "clean.log")
manifest["precompile_snapshot_file"] = "inputs-before.json"
manifest["bundle_origin_path"] = str(bundle.resolve())
manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
PY
report_path="$output_dir/manifest.json"
if [[ ! -f "$report_path" ]]; then report_path="$output_dir/attempt-report.json"; fi
python3 scripts/audit-direct-evidence.py "$version_dir" --manifest "$report_path"
if [[ "$report_path" == *attempt-report.json ]]; then
  printf 'Incomplete direct attempt report: %s\n' "$report_path" >&2
  exit 1
fi
evidence_dir="$version_dir/verification/evidence"
mkdir -p "$evidence_dir"
run_name=$(basename "$run_dir")
cp -a "$output_dir" "$evidence_dir/$run_name"
ln -s "$run_name" "$evidence_dir/latest-direct.next"
python3 - "$evidence_dir/latest-direct.next" "$evidence_dir/latest-direct" <<'PYLINK'
import os, sys
os.replace(sys.argv[1], sys.argv[2])
PYLINK
printf 'Direct evidence bundle: %s/verification/evidence/latest-direct/manifest.json\n' "$version_dir"
