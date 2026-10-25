#!/usr/bin/env python3
"""Execute rooted-slicing regression probes against freshly generated LLBC.

Mutated LLBC is negative-test input only; never an accepted application model.
"""
import argparse
import copy
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser()
p.add_argument('binary', type=Path)
p.add_argument('output', type=Path)
p.add_argument('--llbc', type=Path, required=True,
               help='fresh LLBC from scripts/extract-adapters.py')
a = p.parse_args()
a.output.mkdir(parents=True, exist_ok=False)
original = json.loads(a.llbc.read_text())
commands = []


def execute(label, document, rooted, expected=None, diagnostic=None):
    directory = a.output / label
    directory.mkdir()
    source = directory / 'bytes_adapters.llbc'
    source.write_text(json.dumps(document))
    command = [str(a.binary.resolve()), '-backend', 'lean', '-no-progress-bar',
               '-filter-trait-methods', '-dest', str(directory)]
    if rooted:
        command.append('-rooted-declarations')
    command.append(str(source))
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = result.stdout.decode(errors='replace')
    (directory / 'aeneas.log').write_text(log)
    commands.append({'label': label, 'command': command, 'exit_code': result.returncode})
    if expected == 'success' and result.returncode:
        raise RuntimeError(f'{label}: extraction failed; see {directory}')
    if expected == 'failure' and not result.returncode:
        raise RuntimeError(f'{label}: unexpectedly accepted negative fixture')
    if diagnostic and diagnostic not in log:
        raise RuntimeError(f'{label}: expected diagnostic absent: {diagnostic}')
    outputs = list(directory.glob('*.lean'))
    if expected == 'success':
        if len(outputs) != 1:
            raise RuntimeError(f'{label}: expected one generated Lean file')
        text = outputs[0].read_text()
        if re.search(r'\bsorry\b|\badmit\b|^\s*(?:axiom|opaque|partial\s+def)\b', text, re.M):
            raise RuntimeError(f'{label}: incomplete output')
    return result.returncode, outputs[0].read_bytes() if outputs else None


subset = copy.deepcopy(original)
for f in subset['translated']['fun_decls']:
    if f:
        last = f['item_meta']['name'][-1].get('Ident', [''])[0]
        f['item_meta']['started_from'] = f['item_meta']['is_local'] and last.startswith(('take_', 'chain_'))
execute('six-root-success', subset, True, 'success')
empty = copy.deepcopy(subset)
for f in empty['translated']['fun_decls']:
    if f:
        f['item_meta']['started_from'] = False
execute('empty-roots', empty, True, 'failure', 'requires started_from function roots')
negative = copy.deepcopy(subset)
trait = next(t for t in negative['translated']['trait_decls']
             if t and t['item_meta']['name'][-1].get('Ident', [''])[0] == 'Buf')
omitted_id = next(i for i, m in enumerate(trait['methods'])
                  if m and m['skip_binder']['name'] == 'copy_to_slice')
function = next(f for f in negative['translated']['fun_decls']
                if f and f['item_meta']['name'][-1].get('Ident', [''])[0] == 'remaining'
                and {'Ident': ['take', 0]} in f['item_meta']['name'])


def alter_first_method(node):
    if isinstance(node, dict):
        for key, value in node.items():
            if key == 'Trait' and isinstance(value, list) and len(value) == 2 and value[1] == 0:
                value[1] = omitted_id
                return True
            if alter_first_method(value):
                return True
    elif isinstance(node, list):
        return any(alter_first_method(value) for value in node)
    return False


if not alter_first_method(function['body']):
    raise RuntimeError('Could not construct indirect omitted-method fixture')
execute('reachable-omitted-method', negative, True, 'failure',
        'Reachable method is absent from its registered builtin trait model')
# Without the option, started_from metadata must have no effect at all.
before = execute('no-flag-original', original, False)
after = execute('no-flag-subset', subset, False)
if before != after:
    raise RuntimeError('Without rooted option, root metadata changed output/status')
(a.output / 'result.json').write_text(json.dumps({
    'status': 'regression-passed-not-an-application-proof',
    'commands': commands,
    'checks': ['six real adapter roots extract without placeholders',
               'empty root set rejected', 'indirect omitted model method rejected',
               'without flag root metadata leaves status/output byte-identical'],
    'limitations': 'Negative method fixture intentionally mutates dispatch metadata; it is never promoted. Closure/global/recursive fixture coverage is not exhaustive.'
}, indent=2) + '\n')
print(f'Rooted extraction regressions passed: {a.output}')
