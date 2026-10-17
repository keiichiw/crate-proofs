#!/usr/bin/env python3
"""Package genuine Why3find sessions; never synthesize solver results."""
import importlib.util
import json
from pathlib import Path
import shutil
import sys

VERSION = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('checks', VERSION / 'scripts/check-proofs.py')
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)
spec = importlib.util.spec_from_file_location('audit', VERSION.parent.parent / 'scripts/audit-proof-evidence.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
run = Path(sys.argv[1]).resolve()
root = run / 'coma/verif/percent_encoding_rlib'
inv = json.loads((VERSION / 'verification/target-inventory.json').read_text())
actual = {p.relative_to(root).as_posix()[:-5]: p for p in root.rglob('*.coma')}
checks.require(set(actual) == set(inv['selected']) | set(inv['excluded_generated']), 'Generated inventory mismatch')
checks.require(not inv.get('expected_open'), 'Open targets remain')
before = json.loads((run / 'inputs-before.json').read_text())
checks.snapshot(run / 'inputs-after.json')
after = json.loads((run / 'inputs-after.json').read_text())
for key in ('inputs_sha256', 'tools_sha256'):
    checks.require(before[key] == after[key], f'{key} changed during proof')
checks.require((run / 'prove.exit').read_text().strip() == '0', 'Why3find failed')
checks.require('encoded_array_model' in actual['percent_encode_byte'].read_text(), 'Missing checked encoding dependency')
checks.require('byte_model_subsequence' in actual['impl_PercentDecode_0/next_byte'].read_text(), 'Missing checked decoding dependency')
bundle = run / 'bundle'
bundle.mkdir()
targets = {}
for target, reason in inv['selected'].items():
    coma = actual[target]
    proof = coma.with_suffix('') / 'proof.json'
    modules = json.loads(proof.read_text())['proofs']
    goals = {f'{m}.{g}': tree for m, group in modules.items() for g, tree in group.items()}
    checks.require(goals and all(audit.closed(t) for t in goals.values()), f'Open/empty roots: {target}')
    dest = bundle / target
    dest.mkdir(parents=True)
    shutil.copyfile(coma, dest / 'target.coma')
    shutil.copyfile(proof, dest / 'proof.json')
    targets[target] = dict(goals=len(goals), goal_inventory=sorted(goals), open_goals=[],
        proof_json_sha256=checks.sha(proof), coma_sha256=checks.sha(coma), contract=reason)
for name in ('compile.log', 'prove.log', 'prove.exit', 'versions.txt', 'inputs-before.json', 'inputs-after.json', 'dependency-audit.json'):
    shutil.copyfile(run / name, bundle / name)
shutil.copytree(run / 'native-evidence', bundle / 'native-evidence')
native = {p.name: checks.sha(p) for p in (bundle / 'native-evidence').iterdir()}
manifest = dict(schema='why3find-evidence-v1', cache=False, targets=targets,
    total_session_goals=sum(t['goals'] for t in targets.values()),
    inputs_sha256=before['inputs_sha256'], tools_sha256=before['tools_sha256'],
    expected_open={}, excluded_generated=inv['excluded_generated'], generated_target_count=len(actual),
    command='bash scripts/verify-why3find.sh',
    proof_command='why3find prove --no-cache -f --summary --no-autodetect-provers -P z3,cvc5 -j 2 --fast 1 --time 10 -d 6 SELECTED_COMA_FILES',
    why3_config='scripts/why3.conf',
    dependency_manifest=str(checks.FORM_EVIDENCE), dependency_manifest_sha256=checks.FORM_EVIDENCE_SHA256,
    native_checks_sha256=native, assumption_ledger='verification/assumptions.md',
    log_sha256={n: checks.sha(bundle / n) for n in ('compile.log','prove.log','prove.exit','versions.txt','dependency-audit.json')},
    limitations=['Verification fork only; finite native tests do not prove upstream equivalence.',
                 'Standard-library models, partial ASCII domain, and formatter request-trace limits remain unchanged.'])
(bundle / 'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
print(json.dumps(dict(targets=len(targets), roots=manifest['total_session_goals'], bundle=str(bundle))))
