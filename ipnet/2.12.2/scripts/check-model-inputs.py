#!/usr/bin/env python3
import hashlib,json,os,subprocess
from pathlib import Path
r=Path(__file__).resolve().parents[1]; p=r/'aeneas/profiles/default'
lock=json.loads((p/'toolchain.lock.json').read_text()); inputs=json.loads((p/'std-source-boundaries.json').read_text())
if inputs['rust_toolchain']!=lock['extraction_rust']: raise ValueError('Rust model-source toolchain mismatch')
sysroot=Path(subprocess.check_output(['rustup','run',lock['extraction_rust'],'rustc','--print','sysroot'],text=True).strip())
for name,expected in inputs['files_sha256'].items():
 if hashlib.sha256((sysroot/'lib/rustlib/src/rust/library'/name).read_bytes()).hexdigest()!=expected: raise ValueError('Reviewed Rust standard source differs: '+name)
pin=(Path(os.environ['AENEAS_SOURCE'])/'charon-pin').read_text().strip().splitlines()[-1]
if pin!=lock['repositories']['charon']['revision']: raise ValueError('Aeneas/Charon compatibility pin mismatch')
print('Reviewed standard source hashes and Aeneas/Charon compatibility: OK')
