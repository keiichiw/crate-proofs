#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/env.sh"
cd "$IPNET_ROOT"
repo="$(git rev-parse --show-toplevel)"
mkdir -p verification/runs
run="$(mktemp -d "$IPNET_ROOT/verification/runs/check-XXXXXXXX")"
export CARGO_TARGET_DIR="$run/target"
exec 3>&1
printf 'Local evidence directory: %s\n' "$run" >&3
exec > "$run/run.log" 2>&1
python3 scripts/check-source.py
python3 scripts/check-tools.py
python3 scripts/fingerprint.py > "$run/inputs-before.json"
python3 "$repo/scripts/aeneas-extract.py" "$IPNET_ROOT" --config verification/aeneas.json --output "$run/generated"
python3 - "$run" <<'PY'
import json,sys
from pathlib import Path
run=Path(sys.argv[1])
config=json.loads(Path('verification/aeneas.json').read_text())
llbc=json.loads((run/'generated'/config['llbc']).read_text())
expected=json.loads(Path('verification/toolchain.json').read_text())['extraction_runtime_checks']
assert llbc['translated']['runtime_checks']==expected, 'Unexpected extraction runtime checks'
for name in json.loads(Path('verification/aeneas.json').read_text())['models']:
    assert (run/'generated'/name).read_bytes()==(Path('proofs')/name).read_bytes(), name
PY
cargo test --locked > "$run/native-default.log" 2>&1
cargo test --locked --no-default-features > "$run/native-no-std.log" 2>&1
cargo test --locked --all-features > "$run/native-all-features.log" 2>&1
(cd proofs && lake clean ipnet-proofs) > "$run/lean-clean.log" 2>&1
python3 "$repo/scripts/aeneas-audit.py" "$IPNET_ROOT" --inventory verification/theorems.json --proofs-toml proofs.toml --output "$run/audit"
(cd proofs && lake env lean ../tests/ShiftChecks.lean) > "$run/shift-model-checks.log" 2>&1
python3 scripts/check-source.py
python3 scripts/check-tools.py
python3 scripts/fingerprint.py > "$run/inputs-after.json"
cmp "$run/inputs-before.json" "$run/inputs-after.json"
python3 - "$run" <<'PY'
import hashlib,json,sys
from pathlib import Path
run=Path(sys.argv[1]); inventory=json.loads(Path('verification/theorems.json').read_text())
(run/'result.json').write_text(json.dumps({
 'status':'passed', 'scope':'Only named audited public contracts; see theorem inventory and independent specification.',
 'theorems':inventory['checked'], 'recorder_mappings':inventory['recorder_mappings'],
 'extracted_but_unproved':inventory.get('extracted_but_unproved',[]),
 'native_tests':'Separate finite observations for default and no-default-features.',
 'extraction':'All configured model files regenerated and byte-compared.',
 'freshness':'Local Lake package cleaned; before/after input fingerprints identical.',
 'publication':'Not recorded or published.',
 'files_sha256':{str(p.relative_to(run)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(run.rglob('*')) if p.is_file() and p.name!='run.log'}
},indent=2)+'\n')
PY
printf 'Passed; local evidence: %s\n' "$run" >&3
