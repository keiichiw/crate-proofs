#!/usr/bin/env python3
"""Experimental compiler-only probe; never install its output as a proof model.

Apply normalizer-only.patch to the reviewed core Aeneas tree in a separate clone,
build src/main.exe, then pass that executable and a fresh result directory.
The compressed LLBC is the original extracted body with started_from flags
restricted to the actual unchanged Mut0T.remaining forwarding function.
Guard variants are deliberately mutated negative compiler inputs.
"""
import argparse
import copy
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess

fixture = Path(__file__).resolve().parent
p = argparse.ArgumentParser()
p.add_argument('binary', type=Path)
p.add_argument('output', type=Path)
p.add_argument('--combined-reviewed-tool', action='store_true',
               help='use the separately pinned numeric tool including ordering')
a = p.parse_args()
a.output.mkdir(parents=True, exist_ok=False)
raw = gzip.decompress((fixture / 'reborrow.llbc.gz').read_bytes())
manifest = json.loads((fixture / 'manifest.json').read_text())
assert hashlib.sha256(raw).hexdigest() == manifest['fixture_uncompressed_sha256']
import os
assert a.binary.resolve() == Path(os.environ['AENEAS_NUMERIC_BIN']).resolve(), 'Wrong pinned numeric compiler'

x = json.loads(raw)
cases = [('disabled', x, False), ('enabled', x, True)]
for name in ['extra-use', 'retag', 'mutable-borrow', 'argument-temp', 'nonadjacent']:
    y = copy.deepcopy(x)
    body = y['translated']['fun_decls'][204]['body']['Structured']
    statements = body['body']['statements']
    copy_statement, borrow_statement = statements[3:5]
    if name == 'extra-use':
        st = copy.deepcopy(copy_statement)
        st['kind'] = {'PlaceMention': copy.deepcopy(copy_statement['kind']['Assign'][0])}
        statements.insert(5, st)
    elif name == 'retag':
        copy_statement['kind']['Assign'][1]['Use'][1] = 'Yes'
    elif name == 'mutable-borrow':
        borrow_statement['kind']['Assign'][1]['Ref']['kind'] = 'Mut'
    elif name == 'argument-temp':
        # Also violates the input signature; rejection is weak evidence only.
        body['locals']['arg_count'] = 3
    elif name == 'nonadjacent':
        st = copy.deepcopy(copy_statement)
        st['kind'] = 'Nop'
        statements.insert(4, st)
    cases.append((name, y, True))
results = {}
for name, document, flag in cases:
    directory = a.output / name
    directory.mkdir()
    source = directory / 'bytes_adapters.llbc'
    source.write_text(json.dumps(document))
    command = [str(a.binary.resolve()), '-backend', 'lean', '-no-progress-bar',
               '-filter-trait-methods', '-rooted-declarations', '-dest', str(directory)]
    if flag:
        command.append('-normalize-shared-reborrow')
    command.append(str(source))
    run = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (directory / 'aeneas.log').write_bytes(run.stdout)
    error = b"Can't copy a mutable borrow" in run.stdout
    results[name] = {'exit': run.returncode, 'borrow_copy_error': error, 'command': command}
    if name == 'enabled':
        assert run.returncode == 0 and not error
        model = (directory / 'BytesAdapters.lean').read_text()
        assert not re.search(r'\bsorry\b|\badmit\b|^\s*(?:axiom|opaque|partial\s+def)\b', model, re.M)
    else:
        assert run.returncode != 0
        if name != 'argument-temp':
            assert error
(a.output / 'result.json').write_text(json.dumps({
    'status': 'experimental-compiler-regression-passed-not-an-application-proof',
    'results': results,
    'limitations': ['No general Rust aliasing theorem is proved.',
                    'Argument-temp mutant also has an invalid signature.',
                    'Numeric and full adapter extraction remain separately blocked.',
                    'No accepted core proof depends on this normalization.']
}, indent=2) + '\n')
print(f'Experimental shared-reborrow regressions passed: {a.output}')
