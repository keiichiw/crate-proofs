#!/usr/bin/env python3
"""Extract the unchanged Reader::consume body directly from the release crate."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--output', type=Path, required=True)
out = parser.parse_args().output.resolve()
out.mkdir(parents=True, exist_ok=False)
entry = '{impl alloc::io::buf_read::BufRead for crate::buf::reader::Reader}::consume'
commands = [
    ['charon', 'cargo', '--preset=aeneas', '--remove-unused-clauses',
     '--opaque', 'crate', '--include', 'crate::buf::reader::Reader',
     '--include', 'crate::buf::reader::_::consume', '--start-from', entry,
     '--dest-file', str(out / 'bytes.llbc'), '--', '--lib', '--locked'],
    ['aeneas', '-backend', 'lean', '-filter-trait-methods', '-rooted-declarations',
     '-namespace', 'bytes_reader', '-dest', str(out), str(out / 'bytes.llbc')],
]
for stage, command in zip(['charon', 'aeneas'], commands):
    with (out / (stage + '.log')).open('w') as log:
        subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT, check=True)
assert {p.name for p in out.glob('*.lean')} == {'Bytes.lean'}
source = out / 'Bytes.lean'
text = source.read_text()
assert not re.search(r'(?m)^\s*(?:axiom|opaque|partial\s+def)\b|\b(?:sorry|admit)\b', text), 'Incomplete model rejected'
assert re.findall(r'(?m)^def\s+([^\s({:]+)', text) == [
    'buf.reader.Reader.Insts.AllocIoBuf_readBufRead.consume'], 'Unexpected body scope'
assert re.findall(r'(?m)^structure\s+([^\s({:]+)', text) == ['buf.reader.Reader']
assert re.search(r"Source: '.work/source/src/buf/reader.rs', lines 78:4-80:5", text), 'Original consume provenance missing'
assert 'namespace bytes_reader\n' in text and 'end bytes_reader\n' in text
assert 'let t ← buf_implBufInst.advance self.buf amt\n  ok { buf := t }' in text
assert 'core.io.error.Error' not in text
source.rename(out / 'BytesReader.lean')
(out / 'extraction.json').write_text(json.dumps({
    'status': 'extracted-not-proved', 'commands': commands,
    'scope': 'unchanged upstream Reader BufRead::consume only',
    'interface_projection': 'Buf advance; behavioral assumptions supplied explicitly by proofs',
    'model_change': 'Bytes.lean renamed to BytesReader.lean; contents unchanged',
    'upstream_reader_sha256': hashlib.sha256((root / '.work/source/src/buf/reader.rs').read_bytes()).hexdigest(),
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'files_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                     for p in out.iterdir() if p.is_file()},
}, indent=2) + '\n')
print('Actual Reader::consume extracted:', out)
