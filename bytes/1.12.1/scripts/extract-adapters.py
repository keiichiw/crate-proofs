#!/usr/bin/env python3
"""Extract original adapter/iterator bodies through the reviewed Buf projection."""
import argparse,hashlib,json,re,subprocess
from pathlib import Path
root=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);out=p.parse_args().output.resolve();out.mkdir(parents=True,exist_ok=False)
entries=['take_remaining','take_chunk','take_advance','chain_remaining','chain_chunk','chain_advance','next','slice_remaining','slice_chunk','slice_has_remaining','slice_advance','size_hint','take_has_remaining','chain_has_remaining','concrete_take_remaining','concrete_take_chunk','concrete_take_advance','concrete_chain_remaining','concrete_chain_chunk','concrete_chain_advance','concrete_take_take_advance','concrete_take_chain_advance']
includes=['bytes::buf::take','bytes::buf::chain','bytes::buf::iter','bytes::buf::buf_impl::_','bytes::buf::buf_impl::Buf::has_remaining','bytes::panic_advance','bytes::TryGetError']
commands=[['charon','cargo','--preset=aeneas','--duplicate-defaulted-methods','--remove-unused-self-clauses','--opaque','bytes','--opaque','bytes::buf::buf_impl::Buf']+[a for name in includes for a in ['--include',name]]+[a for name in entries for a in ['--start-from','crate::'+name]]+['--dest-file',str(out/'bytes_adapters.llbc'),'--','--lib','--locked'],['aeneas','-backend','lean','-filter-trait-methods','-rooted-declarations','-dest',str(out),str(out/'bytes_adapters.llbc')]]
for name,cmd in zip(['charon','aeneas'],commands):
 with (out/(name+'.log')).open('w') as log:subprocess.run(cmd,cwd=root/'tests/adapters',stdout=log,stderr=subprocess.STDOUT,check=True)
assert {p.name for p in out.glob('*.lean')}=={'BytesAdapters.lean'}
s=(out/'BytesAdapters.lean').read_text()
assert not re.search(r'(?m)^\s*(?:axiom|opaque|partial\s+def)\b|\b(?:sorry|admit)\b',s),'Incomplete projected extraction rejected'
for name in entries:
 assert re.search(rf'(?m)^def {name}(?=\s|\(|:)',s),name
for mod in ['take','chain']:
 for method in ['remaining','chunk','advance']:
  ty=mod.capitalize();name=f'bytes.buf.{mod}.{ty}.Insts.BytesBufBuf_implBuf.{method}'
  assert re.search(rf'(?m)^def {re.escape(name)}(?=\s|\(|:)',s),name
 assert str(Path('/crate/bytes/1.12.1')/f'.work/source/src/buf/{mod}.rs') in s
assert 'BytesBuf' in s
(out/'extraction.json').write_text(json.dumps({'status':'extracted-not-proved','commands':commands,'scope':'unchanged Take/Chain consuming bodies, IntoIter next/size_hint, concrete slice dictionary leaves','interface_projection':'remaining/chunk/advance/has_remaining only; no behavioral law postulated','files_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in out.iterdir() if p.is_file()}},indent=2)+'\n')
print('Actual adapter bodies extracted:',out)
