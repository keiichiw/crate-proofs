#!/usr/bin/env python3
"""Extract unchanged Cursor Buf and transparent std Cursor/AsRef bodies."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser()
p.add_argument('--output', type=Path, required=True)
out = p.parse_args().output.resolve()
out.mkdir(parents=True, exist_ok=False)
includes = [
    'bytes::TryGetError', 'bytes::min_u64_usize', 'bytes::saturating_sub_usize_u64',
    'bytes::panic_advance', 'bytes::buf::buf_impl::_::remaining',
    'bytes::buf::buf_impl::_::chunk', 'bytes::buf::buf_impl::_::advance',
    'core::io::cursor::Cursor', 'core::io::cursor::_::get_ref',
    'core::io::cursor::_::position', 'core::io::cursor::_::set_position',
    'core::convert::num::ptr_try_from_impls', 'core::convert::_::as_ref',
]
command = ['charon', 'cargo', '--preset=aeneas', '--remove-unused-clauses', '--opaque', 'bytes']
command += [arg for name in includes for arg in ['--include', name]]
command += [arg for name in ['remaining', 'chunk', 'advance'] for arg in ['--start-from', 'crate::' + name]]
command += ['--dest-file', str(out / 'bytes_cursor_slice.llbc'), '--', '--lib', '--locked']
commands = [command, ['aeneas', '-backend', 'lean', '-filter-trait-methods',
                     '-rooted-declarations', '-dest', str(out), str(out / 'bytes_cursor_slice.llbc')]]
env = dict(os.environ, CARGO_TARGET_DIR=str(root / '.work/build/cursor-capture'))
for label, command in zip(['charon', 'aeneas'], commands):
    with (out / (label + '.log')).open('w') as log:
        subprocess.run(command, cwd=root / 'tests/cursor', env=env,
                       stdout=log, stderr=subprocess.STDOUT, check=True)
assert {p.name for p in out.glob('*.lean')} == {'BytesCursorSlice.lean'}
source = (out / 'BytesCursorSlice.lean').read_text()
assert not re.search(r'(?m)^\s*(?:axiom|opaque|partial\s+def)\b|\b(?:sorry|admit)\b', source), 'Incomplete extraction rejected'
for name in ['remaining', 'chunk', 'advance',
             'core.io.cursor.Cursor.get_ref', 'core.io.cursor.Cursor.position',
             'core.io.cursor.Cursor.set_position',
             'core.io.cursor.Cursor.Insts.BytesBufBuf_implBuf.remaining',
             'core.io.cursor.Cursor.Insts.BytesBufBuf_implBuf.chunk',
             'core.io.cursor.Cursor.Insts.BytesBufBuf_implBuf.advance',
             'Shared0T.Insts.CoreConvertAsRef.as_ref',
             'Slice.Insts.CoreConvertAsRefSlice.as_ref']:
    assert re.search(rf'(?m)^def {re.escape(name)}(?=\s|\(|:)', source), name
for origin in [str(Path('/crate/bytes/1.12.1') / '.work/source/src/buf/buf_impl.rs'),
               '/rustc/library/core/src/io/cursor.rs', '/rustc/library/core/src/convert/mod.rs']:
    assert origin in source, origin
(out / 'extraction.json').write_text(json.dumps({
    'status': 'extracted-not-proved', 'commands': commands,
    'features': 'default-features=true, explicit std',
    'scope': 'actual Cursor Buf methods and transparent original std Cursor/AsRef bodies',
    'wrapper_role': 'dispatch only; no implementation replacement',
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'files_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                     for p in out.iterdir() if p.is_file()},
}, indent=2) + '\n')
print('Actual Cursor implementations extracted:', out)
