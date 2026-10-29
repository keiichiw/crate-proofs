#!/usr/bin/env python3

from source_coordinates import canonicalize
from pathlib import Path as _Path
import os as _os
PROFILE = _Path(__file__).resolve().parents[1]
CRATE = PROFILE.parents[2]
"""Source-backed generic body extraction with checked GAT normalization and local-display alpha normalization."""
import argparse,hashlib,json,pathlib,re,subprocess,sys
R=PROFILE;V=CRATE
p=argparse.ArgumentParser();p.add_argument('--output',required=True);a=p.parse_args();D=pathlib.Path(a.output).resolve();D.mkdir(parents=True,exist_ok=False)
config=R/'config/body.json';raw=config.read_bytes();cfg=json.loads(raw)
expected=['crate::_::'+n for n in ['new','checksum','update','digest','digest_with_initial','table','finalize']]
assert cfg['entries']==expected
commands=[['charon','cargo','--rustc-arg=--remap-path-prefix='+str(CRATE)+'=crc-3.4.0','--preset=aeneas','--remove-unused-clauses','--no-dedup-serialized-ast',*[v for e in expected for v in ['--start-from',e]],'--dest-file',str(D/'original.llbc'),'--','--lib','--locked'],[sys.executable,str(R/'adapter/normalize-gat.py'),str(D/'original.llbc'),str(D/'crc_body.llbc')],[sys.executable,str(R/'adapter/check-normalization.py'),str(D/'original.llbc'),str(D/'crc_body.llbc'),'--output',str(D/'correspondence.json')],['aeneas','-backend','lean','-split-files','-namespace','CrcBody','-dest',str(D),str(D/'crc_body.llbc')]]
for label,cmd in zip(['charon','normalize','correspondence','aeneas'],commands):
 with (D/f'{label}.log').open('w') as log:subprocess.run(cmd,cwd=V,stdout=log,stderr=subprocess.STDOUT,check=True)
 if label=='charon':canonicalize(D/'original.llbc',CRATE,V)
assert {p.name for p in D.glob('*.lean')}=={'Types.lean','Funs.lean','FunsExternal_Template.lean'}
for f in ['Types.lean','Funs.lean']:
 s=(D/f).read_text();assert not re.search(r'(?m)^\s*(?:axiom|opaque|partial\s+def)\b|\b(?:sorry|admit)\b',s)
 for name in cfg['models'].get(f,[]):assert re.search(rf'(?m)^def {re.escape(name)}(?=\s|\(|:)',s),name
external=re.findall(r'^axiom (\S+)',(D/'FunsExternal_Template.lean').read_text(),re.M)
assert external==[f'core.num.U{n}.reverse_bits' for n in [8,16,32,64,128]],external
assert config.read_bytes()==raw
(D/'extraction.json').write_text(json.dumps({'status':'extracted-with-explicit-type-adapter-and-standard-model-boundary','commands':commands,'configuration_sha256':hashlib.sha256(raw).hexdigest(),'files_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(D.iterdir()) if p.is_file()}},indent=2)+'\n')
print('PASS all original public bodies; independently checked type and display normalization; five standard reverse_bits boundaries')
