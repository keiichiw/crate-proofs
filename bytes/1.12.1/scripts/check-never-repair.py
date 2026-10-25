#!/usr/bin/env python3
"""Regression test the exact Never-continuation repair, not a buffer proof."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
BASELINE = Path(os.environ['AENEAS_ORDINARY_BIN'])


def main():
    patched = Path(sys.argv[1]) if len(sys.argv) > 1 else (
        Path(os.environ['AENEAS_SOURCE']) / 'bin/aeneas')
    if len(sys.argv) > 2:
        run = Path(sys.argv[2]).resolve()
        run.mkdir(parents=True, exist_ok=False)
    else:
        run = Path(tempfile.mkdtemp(prefix='never-regression-', dir=ROOT / 'aeneas/profiles/default/runs'))
    fixture = ROOT / 'aeneas/profiles/default/patches/never-regression'
    commands = []
    command = ['charon', 'cargo', '--preset=aeneas', '--dest-file',
               str(run / 'never_regression.llbc'), '--', '--lib', '--locked']
    env = dict(os.environ, CARGO_TARGET_DIR=str(ROOT / '.work/build/never-regression'))
    with (run / 'charon.log').open('w') as log:
        subprocess.run(command, cwd=fixture, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    commands.append({'stage': 'charon', 'command': command, 'exit_code': 0})
    sources = {}
    for label, binary, expected in [('baseline', BASELINE, 1), ('patched', patched, 0)]:
        destination = run / label
        destination.mkdir()
        command = [str(binary), '-backend', 'lean', '-no-progress-bar', '-dest',
                   str(destination), str(run / 'never_regression.llbc')]
        with (destination / 'aeneas.log').open('w') as log:
            result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
        commands.append({'stage': label, 'command': command, 'exit_code': result.returncode})
        if result.returncode != expected:
            raise ValueError(f'{label}: expected exit {expected}, observed {result.returncode}; {run}')
        sources[label] = (destination / 'NeverRegression.lean').read_text()
    if 'Unexpected result: Cps.Unit' not in (run / 'baseline/aeneas.log').read_text():
        raise ValueError('Baseline did not reproduce the expected defect')
    if re.search(r'\bsorry\b|^\s*(?:axiom|opaque|partial\s+def)\b', sources['patched'], re.M):
        raise ValueError('Repaired regression contains incomplete/axiomatized output')
    pattern = r'def ordinary.*?(?=\n/--|\nend never_regression)'
    if re.search(pattern, sources['baseline'], re.S).group() != re.search(pattern, sources['patched'], re.S).group():
        raise ValueError('Ordinary non-Never operation changed')
    (run / 'result.json').write_text(json.dumps({
        'status': 'regression-passed-not-an-application-proof',
        'commands': commands,
        'checks': ['terminal Never defect reproduced',
                   'panic and recursive-divergence call bodies translate',
                   'no application axioms/placeholders', 'ordinary body unchanged'],
    }, indent=2) + '\n')
    print(f'Never-continuation regression passed: {run}')


if __name__ == '__main__':
    main()
