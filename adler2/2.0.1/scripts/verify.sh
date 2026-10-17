#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/env.sh"
cd "$ADLER_ROOT"
run="$(mktemp -d "$ADLER_ROOT/verification/runs/check-XXXXXXXX")"
exec 3>&1 4>&2
printf 'Local evidence directory: %s\n' "$run" >&3
exec > "$run/run.log" 2>&1
python3 scripts/check-source.py
python3 scripts/check-tools.py
python3 scripts/sync-theorems.py --check
python3 scripts/fingerprint.py > "$run/inputs-before.json"
bash scripts/extract.sh "$run/generated"
cmp "$run/generated/Adler2.lean" proofs/Adler2.lean
cargo test --locked 2>&1 | tee "$run/native-default.log"
cargo test --locked --no-default-features 2>&1 | tee "$run/native-no-std.log"
cd proofs
lake clean adler2-proofs
lake build Proofs 2>&1 | tee "$run/lean-build.log"
lake env lean Proofs/Audit.lean 2>&1 | tee "$run/lean-audit.log"
lake env lean Proofs/RecorderAudit.lean 2>&1 | tee "$run/recorder-audit.log"
cd "$ADLER_ROOT"
python3 scripts/check-source.py
python3 scripts/check-tools.py
python3 scripts/sync-theorems.py --check
python3 scripts/fingerprint.py > "$run/inputs-after.json"
cmp "$run/inputs-before.json" "$run/inputs-after.json"
python3 - "$run" <<'PY'
import hashlib, json, re, sys
from pathlib import Path
run = Path(sys.argv[1])
root = Path.cwd()
inventory = json.loads((root/'verification/theorems.json').read_text())
expected = [item['name'] for item in inventory['checked']]
audited = re.findall(r'^AUDIT OK: ([A-Za-z_][A-Za-z_0-9.]*)\b;', (run/'lean-audit.log').read_text(), re.M)
if audited != expected:
    raise SystemExit(f'theorem audit mismatch: expected {expected}, observed {audited}')
mapped = [item['theorem'] for item in inventory['recorder_mappings']]
recorded = re.findall(r'^proofs\.rs:checked:([A-Za-z_][A-Za-z_0-9.]*)$', (run/'recorder-audit.log').read_text(), re.M)
if recorded != mapped:
    raise SystemExit(f'recorder audit mismatch: expected {mapped}, observed {recorded}')
(run/'result.json').write_text(json.dumps({
 'status': 'passed', 'scope': 'actual optimized Adler-32 compute, arbitrary-state slice update, one-shot checksum, codec, split/resume laws, and selected prerequisites',
 'theorems': inventory['checked'],
 'recorder_mappings': inventory['recorder_mappings'],
 'extracted_but_unproved': inventory['extracted_but_unproved'],
 'native_tests': 'separate finite observations, default and no_std',
 'extraction': 'regenerated and byte-compared with proofs/Adler2.lean',
 'freshness': 'input fingerprints equal before/after; local Lake targets cleaned',
 'cargo_proofs_recording': 'not run: pinned CLI lacks submodule initialization; future recording also requires committed and pushed inputs',
 'files_sha256': {str(p.relative_to(run)): hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in sorted(run.rglob('*')) if p.is_file() and p.name != 'run.log'}
}, indent=2)+'\n')
PY
printf 'Passed; local evidence: %s\n' "$run" >&3
