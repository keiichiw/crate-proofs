#!/usr/bin/env bash
set -euo pipefail
version_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
repo_dir=$(cd -- "$version_dir/../.." && pwd)
cd "$version_dir"
source "$repo_dir/scripts/activate.sh"
export WHY3CONFIG="$version_dir/scripts/why3.conf"
export DUNE_DIR_LOCATIONS="why3find:lib:$XDG_DATA_HOME/creusot/share/why3find"
if (($#)); then echo "usage: $0" >&2; exit 2; fi

mkdir -p "$version_dir/verif"
run_dir=$(mktemp -d "$version_dir/verif/why3find-XXXXXXXX")
mkdir -p "$run_dir/coma" "$run_dir/target"
printf 'Fresh proof attempt: %s\n' "$run_dir"

dependency_dir="$repo_dir/form_urlencoded/1.2.2"
python3 "$repo_dir/scripts/audit-proof-evidence.py" "$dependency_dir" \
  --manifest "$(python3 - <<'PYPIN'
import importlib.util
s=importlib.util.spec_from_file_location('check','scripts/check-proofs.py'); m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
print(m.FORM_EVIDENCE)
PYPIN
)" --reconstruct-root-goals \
  >"$run_dir/dependency-audit.json"
{ cargo creusot version; rustc -Vv; why3find --version; why3 --version; z3 --version; cvc5 --version; } >"$run_dir/versions.txt" 2>&1
# Refresh native logs in this invocation, before they enter the proof fingerprint.
CARGO_TARGET_DIR="$run_dir/native-target" bash verification/differential/run-full-scope.sh \
  >"$run_dir/native-run.log" 2>&1
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
(cd "$version_dir/crate" && cargo creusot --only=coma --span-mode absolute \
  --output-dir "$run_dir/coma" -- --locked --offline --target-dir "$run_dir/target") \
  >"$run_dir/compile.log" 2>&1

mapfile -t targets < <(python3 - "$version_dir/verification/target-inventory.json" "$run_dir/coma/verif/percent_encoding_rlib" <<'PYTARGET'
import json,sys
from pathlib import Path
for target in sorted(json.loads(Path(sys.argv[1]).read_text())['selected']):
    print(Path(sys.argv[2]) / (target+'.coma'))
PYTARGET
)
[[ ${#targets[@]} -gt 0 ]]
set +e
why3find prove --no-cache -f --summary --no-autodetect-provers -P z3,cvc5 -j 2 --fast 1 --time 10 -d 6 "${targets[@]}" >"$run_dir/prove.log" 2>&1
proof_status=$?
set -e
printf '%s\n' "$proof_status" >"$run_dir/prove.exit"
[[ "$proof_status" == 0 ]] || { tail -40 "$run_dir/prove.log"; exit "$proof_status"; }
python3 scripts/package-why3find.py "$run_dir"
python3 "$repo_dir/scripts/audit-proof-evidence.py" "$version_dir" --manifest "$run_dir/bundle/manifest.json" --generated-dir "$run_dir/coma/verif/percent_encoding_rlib" --reconstruct-root-goals >"$run_dir/bundle/audit.json"
evidence_dir="$version_dir/verification/evidence"
run_name=$(basename "$run_dir")
cp -a "$run_dir/bundle" "$evidence_dir/$run_name"
python3 "$repo_dir/scripts/audit-proof-evidence.py" "$version_dir" --manifest "$evidence_dir/$run_name/manifest.json" --reconstruct-root-goals >"$evidence_dir/$run_name/archive-audit.json"
python3 - "$evidence_dir" "$run_name" <<'PYLINK'
import os,sys
from pathlib import Path
root=Path(sys.argv[1])
(root/'latest-why3find.next').symlink_to(sys.argv[2])
os.replace(root/'latest-why3find.next',root/'latest-why3find')
PYLINK
printf 'Why3find evidence: %s/%s/manifest.json\n' "$evidence_dir" "$run_name"
