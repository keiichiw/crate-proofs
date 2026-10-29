#!/usr/bin/env python3
"""Extract the original five util bodies with portable rustc source coordinates."""
from source_coordinates import canonicalize
from pathlib import Path
import argparse, hashlib, json, re, subprocess
P=Path(__file__).resolve().parents[1];R=P.parents[2]
p=argparse.ArgumentParser();p.add_argument('--output',required=True,type=Path);a=p.parse_args()
out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
cfg=json.loads((P/'config/aeneas.json').read_text())
entries=[f'crate::util::crc{n}' for n in [8,16,32,64,128]]
assert cfg['entries']==entries
assert cfg['local_scope']=={'opaque_crate':True,'include':entries}
commands=[['charon','cargo','--rustc-arg=--remap-path-prefix='+str(R)+'=crc-3.4.0','--preset=aeneas',*[a for e in entries for a in ['--start-from',e]],'--opaque','crate',*[a for e in entries for a in ['--include',e]],'--remove-unused-clauses','--dest-file',str(out/'crc.llbc'),'--','--lib','--locked'],['aeneas','-backend','lean','-dest',str(out),str(out/'crc.llbc')]]
for label,cmd in zip(['charon','aeneas'],commands):
 with (out/(label+'.log')).open('w') as f:subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT,check=True)
 if label=='charon':canonicalize(out/'crc.llbc',R,R)
assert not json.loads((out/'crc.llbc').read_text())['has_errors']
assert {x.name for x in out.glob('*.lean')}==set(cfg['models'])
for name,defs in cfg['models'].items():
 text=(out/name).read_text()
 assert not re.search(r'(?m)^\s*(?:axiom|opaque|partial\s+def)\b|\b(?:sorry|admit)\b',text)
 for d in defs:assert re.search(r'(?m)^def '+re.escape(d)+r'(?=\s|\(|:)',text),d
(out/'extraction.json').write_text(json.dumps({'commands':commands,'config_sha256':hashlib.sha256((P/'config/aeneas.json').read_bytes()).hexdigest(),'status':'extracted-not-proved'},indent=2)+'\n')
