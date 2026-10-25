#!/usr/bin/env python3
"""Extract the unchanged private range helper using the reviewed stage3 options."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

root = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser()
p.add_argument('--output', type=Path, required=True)
p.add_argument('--aeneas', type=Path, required=True, help='pinned stage3 Aeneas executable')
a = p.parse_args()
out = a.output.resolve()
out.mkdir(parents=True, exist_ok=False)
binary = a.aeneas.resolve()
commands = [
    ['charon', 'cargo', '--preset=aeneas', '--opaque', 'crate', '--include',
     'crate::range', '--start-from', 'crate::range', '--dest-file',
     str(out / 'bytes_range.llbc'), '--', '--lib', '--locked'],
    [str(binary), '-backend', 'lean', '-namespace', 'bytes_range',
     '-disable-branch-joins', '-lean-import', 'BytesStage3Formatting',
     '-dest', str(out), str(out / 'bytes_range.llbc')],
]
records = []
for label, command in zip(['charon', 'aeneas'], commands):
    with (out / (label + '.log')).open('w') as log:
        subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT, check=True)
    executable = Path(shutil.which(command[0]) or command[0]).resolve()
    records.append({'stage': label, 'command': command, 'exit_code': 0,
                    'executable': str(executable),
                    'executable_sha256': hashlib.sha256(executable.read_bytes()).hexdigest()})
assert {f.name for f in out.glob('*.lean')} == {'BytesRange.lean'}
source = (out / 'BytesRange.lean').read_text()
assert not re.search(r'(?m)^\s*(?:axiom|opaque|partial\s+def)\b|\b(?:sorry|admit)\b', source), 'Incomplete extraction rejected'
assert re.search(r'(?m)^def range(?=\s|\(|:)', source)
assert 'namespace bytes_range' in source
assert '.work/source/src/lib.rs' in source and '/rustc/library/core/src/ops/range.rs' in source
assert 'public import BytesStage3Formatting' in source
assert 'new_debug_without_dictionary' in source
assert 'core.fmt.DebugUsize' not in source, 'Discarded formatting dictionary leaked into generated model'
(out / 'extraction.json').write_text(json.dumps({
    'status': 'extracted-not-proved', 'stages': records,
    'scope': 'actual unchanged private range helper; explicit query dictionary remains',
    'translation_option': 'branch-specific contexts and original continuations; no marker sanity check disabled',
    'formatting_boundary': 'exact rfl erasure of already unused Debug dictionary; no text-formatting claim',
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'files_sha256': {f.name: hashlib.sha256(f.read_bytes()).hexdigest()
                     for f in out.iterdir() if f.is_file()},
}, indent=2) + '\n')
print('Actual range helper extracted:', out)
