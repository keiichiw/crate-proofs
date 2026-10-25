#!/usr/bin/env python3
"""Extract the original checked loop with an exact structural error model."""
import argparse,hashlib,json,re,subprocess
from pathlib import Path
root=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('--aeneas',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
a=p.parse_args();out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
includes=['crate::buf::buf_impl::Buf::try_copy_to_slice','crate::buf::buf_impl::Buf::has_remaining','crate::buf::buf_impl::_','crate::TryGetError']
cmds=[['charon','cargo','--preset=aeneas','--remove-unused-clauses','--remove-unused-self-clauses','--opaque','crate','--opaque','crate::buf::buf_impl::Buf']+[v for n in includes for v in ['--include',n]]+['--start-from','crate::buf::buf_impl::Buf::try_copy_to_slice','--dest-file',str(out/'bytes.llbc'),'--','--lib','--locked'],[str(a.aeneas.resolve()),'-backend','lean','-namespace','bytes_extended_copy','-lean-import','BytesStage3Types','-normalize-shared-reborrow','-order-projected-declarations','-rooted-declarations','-filter-trait-methods','-dest',str(out),str(out/'bytes.llbc')]]
for name,cmd in zip(['charon','aeneas'],cmds):
 with(out/(name+'.log')).open('w')as log:subprocess.run(cmd,cwd=root,stdout=log,stderr=subprocess.STDOUT,check=True)
assert {p.name for p in out.glob('*.lean')}=={'Bytes.lean'}
s=(out/'Bytes.lean').read_text()
assert not re.search(r'(?m)^\s*(?:axiom|opaque|partial\s+def)\b|\b(?:sorry|admit)\b',s)
assert 'Generated the partial file' not in (out/'aeneas.log').read_text()
for n in ['buf.buf_impl.Buf.try_copy_to_slice.default_loop.body','buf.buf_impl.Buf.try_copy_to_slice.default_loop','buf.buf_impl.Buf.try_copy_to_slice.default']:
 assert re.search(rf'(?m)^def {re.escape(n)}(?=\s|\(|:)',s),n
assert "Source: '.work/source/src/buf/buf_impl.rs'" in s
(out/'BytesExtendedCopy.lean').write_bytes((out/'Bytes.lean').read_bytes())
assert (out/'BytesExtendedCopy.lean').read_bytes()==(out/'Bytes.lean').read_bytes()
assert {p.name for p in out.glob('*.lean')}=={'Bytes.lean','BytesExtendedCopy.lean'}
(out/'extraction.json').write_text(json.dumps({'status':'extracted-not-proved','commands':cmds,'scope':'actual defaultcheckedcopy loop with law-free five-method interface and exact two-field error representation','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'files_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in out.iterdir()if p.is_file()}},indent=2)+'\n')
print(out)
