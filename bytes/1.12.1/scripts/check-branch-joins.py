#!/usr/bin/env python3
"""Freshly extract safe join regression fixture; compare frozen/stage3 compiler.
All failed/partial outputs remain diagnostic only.
"""
import argparse
import json
import os
import re
import shutil
from pathlib import Path
import subprocess

p = argparse.ArgumentParser()
p.add_argument('baseline', type=Path)
p.add_argument('patched', type=Path)
p.add_argument('output', type=Path)
a = p.parse_args()
a.output.mkdir(parents=True, exist_ok=False)
root = Path(__file__).resolve().parents[1]
fixture = root / 'aeneas/profiles/default/patches/branch-join-regression'
cargo_env = dict(os.environ, CARGO_TARGET_DIR=str(root / '.work/build/branch-join-regression'))
source = a.output / 'range_join_minimal.llbc'
command = ['charon', 'cargo', '--preset=aeneas', '--dest-file', str(source), '--', '--lib', '--locked']
with (a.output / 'charon.log').open('w') as log:
    subprocess.run(command, cwd=fixture, env=cargo_env, stdout=log, stderr=subprocess.STDOUT, check=True)
control_source = a.output / 'controls/range_join_minimal.llbc'
control_source.parent.mkdir()
control_command = ['charon', 'cargo', '--preset=aeneas']
for name in ['bound_value', 'trait_bound', 'trait_bound_simple', 'mutable_path', 'checked_path', 'early_return', 'break_path']:
    control_command += ['--start-from', 'crate::' + name]
control_command += ['--dest-file', str(control_source), '--', '--lib', '--locked']
with (a.output / 'controls-charon.log').open('w') as log:
    subprocess.run(control_command, cwd=fixture, env=cargo_env, stdout=log, stderr=subprocess.STDOUT, check=True)
records, generated = [], {}
for label, binary, flags, src, expected in [
    ('baseline-controls', a.baseline, [], control_source, 0),
    ('patched-controls-flagoff', a.patched, [], control_source, 0),
    ('patched-flagoff-fails', a.patched, [], source, 1),
    ('patched-enabled', a.patched, ['-disable-branch-joins'], source, 0),
]:
    directory = a.output / label
    directory.mkdir()
    command = [str(binary.resolve()), '-backend', 'lean', '-no-progress-bar', '-dest', str(directory)] + flags + [str(src)]
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (directory / 'aeneas.log').write_bytes(result.stdout)
    assert result.returncode == expected, (label, result.returncode)
    records.append({'label': label, 'command': command, 'exit_code': result.returncode})
    text = (directory / 'RangeJoinMinimal.lean').read_text()
    generated[label] = text
    if not expected:
        assert 'sorry' not in text and '\naxiom ' not in text
assert generated['baseline-controls'] == generated['patched-controls-flagoff']
# Compile the freshly generated enabled model and its maintained semantic checks.
proofs = Path(os.environ['AENEAS_PROOF_DIR'])
enabled = a.output / 'patched-enabled'
proof_source = enabled / 'JoinRegression.lean'
proof_source.write_bytes((fixture / 'JoinRegression.lean').read_bytes())
lake_path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=proofs, text=True).strip()
lean = subprocess.check_output(['lake', 'env', 'which', 'lean'], cwd=proofs, text=True).strip()
env = dict(os.environ, LEAN_PATH=str(enabled.resolve()) + ':' + lake_path)
for module in ['RangeJoinMinimal', 'JoinRegression']:
    command = [lean, '-R', str(enabled.resolve()), '-o', str((enabled / (module + '.olean')).resolve()), str((enabled / (module + '.lean')).resolve())]
    with (enabled / (module + '.log')).open('w') as log:
        subprocess.run(command, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    records.append({'label': 'lean-' + module, 'command': command, 'exit_code': 0})
theorems = re.findall(r'^theorem (\w+)', proof_source.read_text(), re.M)
audit = enabled / 'Audit.lean'
audit.write_text('import JoinRegression\n' + ''.join('#print axioms join_regression.' + n + '\n' for n in theorems))
command = [lean, '-R', str(enabled.resolve()), str(audit.resolve())]
run = subprocess.run(command, env=env, capture_output=True, text=True, check=True)
(enabled / 'audit.log').write_text(run.stdout + run.stderr)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for declaration, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", run.stdout):
    assert set(x.strip() for x in axioms.split(',') if x.strip()) <= allowed, (declaration, axioms)
assert len(re.findall(r"depends on axioms:|does not depend on any axioms", run.stdout)) == len(theorems)
records.append({'label': 'lean-axiom-audit', 'command': command, 'exit_code': 0})
(a.output / 'results.json').write_text(json.dumps({'status': 'compiler regression only, not upstream range proof', 'commands': records, 'checks': ['flagoff safe controls byte-identical to frozen core', 'flagoff original failure preserved', 'enabled complete actual fixture translation', 'fresh generated model and callback/mutable-state/overflow/return/break semantic proofs rebuilt', 'axiom audit only permitted foundational axioms']}, indent=2) + '\n')
print(a.output)
