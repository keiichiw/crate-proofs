#!/usr/bin/env python3
"""Extract the unchanged generic checked copy loop, without default duplication."""
import argparse,hashlib,json,re,subprocess
from pathlib import Path
root=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
out=p.parse_args().output.resolve();out.mkdir(parents=True,exist_ok=False)
includes=['crate::buf::buf_impl::Buf::try_copy_to_slice','crate::buf::buf_impl::Buf::has_remaining','crate::buf::buf_impl::_','crate::TryGetError','crate::panic_advance']
commands=[['charon','cargo','--preset=aeneas','--remove-unused-clauses','--remove-unused-self-clauses','--opaque','crate','--opaque','crate::buf::buf_impl::Buf']+[v for name in includes for v in ['--include',name]]+['--start-from','crate::buf::buf_impl::Buf::try_copy_to_slice','--dest-file',str(out/'bytes.llbc'),'--','--lib','--locked'],['aeneas','-backend','lean','-namespace','bytes_copy','-filter-trait-methods','-rooted-declarations','-dest',str(out),str(out/'bytes.llbc')]]
for name,cmd in zip(['charon','aeneas'],commands):
 with (out/(name+'.log')).open('w') as log:subprocess.run(cmd,cwd=root,stdout=log,stderr=subprocess.STDOUT,check=True)
assert {p.name for p in out.glob('*.lean')} == {'Bytes.lean'}, 'Unexpected generated model inventory'
s=(out/'Bytes.lean').read_text()
assert not re.search(r'(?m)^\s*(?:axiom|opaque|partial\s+def)\b|\b(?:sorry|admit)\b',s)
for name in ['buf.buf_impl.Buf.try_copy_to_slice.default_loop.body','buf.buf_impl.Buf.try_copy_to_slice.default_loop','buf.buf_impl.Buf.try_copy_to_slice.default']:
 assert re.search(rf'(?m)^def {re.escape(name)}(?=\s|\(|:)',s),name
# The original crate determines filename Bytes.lean; namespace is an extractor option.
# Rename only the file; generated content is copied byte for byte.
(out/'BytesCopy.lean').write_bytes((out/'Bytes.lean').read_bytes())
assert {p.name for p in out.glob('*.lean')} == {'Bytes.lean','BytesCopy.lean'}
assert (out/'BytesCopy.lean').read_bytes() == (out/'Bytes.lean').read_bytes()
(out/'extraction.json').write_text(json.dumps({'commands':commands,'status':'extracted-not-proved','source':'unchanged release Buf::try_copy_to_slice body and loop','generated_sha256':hashlib.sha256((out/'BytesCopy.lean').read_bytes()).hexdigest(),'file_rename':'Bytes.lean to BytesCopy.lean, identical bytes'},indent=2)+'\n')
print('Actual checked copy loop extracted:',out)
