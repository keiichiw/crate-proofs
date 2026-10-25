#!/usr/bin/env python3
"""Capture actual upstream concrete slice Buf bodies through calling wrappers."""
import argparse,hashlib,json,re,subprocess
from pathlib import Path
root=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);args=p.parse_args()
out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
commands=[['charon','cargo','--preset=aeneas','--opaque','bytes','--include','bytes::buf::buf_impl::_::advance','--include','bytes::buf::buf_impl::_::copy_to_slice','--include','bytes::panic_advance','--include','bytes::TryGetError','--start-from','crate::advance_slice','--start-from','crate::copy_slice','--dest-file',str(out/'bytes_consumption.llbc'),'--','--lib','--locked'],['aeneas','-backend','lean','-dest',str(out),str(out/'bytes_consumption.llbc')]]
for label,cmd in zip(['charon','aeneas'],commands):
 with (out/(label+'.log')).open('w') as log:subprocess.run(cmd,cwd=root/'tests/consumption',stdout=log,stderr=subprocess.STDOUT,check=True)
assert {p.name for p in out.glob('*.lean')}=={'BytesConsumption.lean'}
s=(out/'BytesConsumption.lean').read_text()
assert not re.search(r'(?m)^\s*(?:axiom|opaque|partial\s+def)\b|\b(?:sorry|admit)\b',s),'Partial/unmodeled output rejected'
for name in ['bytes.panic_advance','Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance','Shared0SliceU8.Insts.BytesBufBuf_implBuf.copy_to_slice','advance_slice','copy_slice']:
 assert re.search(rf'(?m)^def {re.escape(name)}(?=\s|\(|:)',s),name
assert str(Path('/crate/bytes/1.12.1')/'.work/source/src/buf/buf_impl.rs') in s,'Upstream implementation provenance absent'
assert 'new_display_without_dictionary' in s,'Reviewed unused-dictionary model not selected'
(out/'extraction.json').write_text(json.dumps({'status':'extracted-not-proved','commands':commands,'wrapper_role':'calls actual unchanged upstream concrete slice Buf methods; contains no implementation replacement','features':'bytes default-features=false','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'files_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in out.iterdir() if p.is_file()}},indent=2)+'\n')
print('Actual concrete slice implementations extracted:',out)
