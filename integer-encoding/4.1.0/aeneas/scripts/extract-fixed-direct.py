#!/usr/bin/env python3
"""Extract unchanged FixedInt bodies, retaining explicitly modeled standard boundaries."""
from pathlib import Path
import argparse,json,re,subprocess,hashlib,os
R=Path(__file__).resolve().parents[1];p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=Path(os.environ['AENEAS_RUN_DIR'])/'fixed-direct');a=p.parse_args();D=a.output.resolve();D.mkdir(parents=True,exist_ok=False); env=dict(os.environ,RUSTUP_TOOLCHAIN=os.environ['AENEAS_EXTRACT_RUST'])
cp=R/'aeneas/profiles/default/fixed-direct.json';raw=cp.read_bytes();cfg=json.loads(raw)
expected=['{impl crate::fixed::FixedInt for _}::'+n for n in ('encode_fixed','decode_fixed','encode_fixed_light','switch_endianness')]
assert cfg['entries']==expected and cfg['namespace']=='IntegerFixedDirect' and cfg['llbc']=='integer_fixed_direct.llbc'
assert cfg['external_standard_boundaries']==['core.mem.size_of','core.slice.Slice.clone_from_slice']
commands=[['charon','cargo','--preset=aeneas','--remove-unused-clauses',*[v for n in expected for v in ('--start-from',n)],'--opaque','crate',*[v for n in expected for v in ('--include',n)],'--dest-file',str(D/cfg['llbc']),'--','--lib','--locked'],['aeneas','-backend','lean','-split-files','-namespace',cfg['namespace'],'-dest',str(D),str(D/cfg['llbc'])]]
for label,c in zip(('charon','aeneas'),commands):
 with (D/(label+'.log')).open('w') as f:subprocess.run(c,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT,check=True)
assert {f.name for f in D.glob('*.lean')}=={'Types.lean','Funs.lean','FunsExternal_Template.lean'}
for name,defs in cfg['model_files'].items():
 s=(D/name).read_text();assert not re.search(r'(?m)^\s*(?:axiom|opaque|partial\s+def)\b|\b(?:sorry|admit)\b',s)
 assert re.findall(r'^def ([\w.]+)',s,re.M)==defs,name
external=re.findall(r'^axiom ([\w.]+)',(D/'FunsExternal_Template.lean').read_text(),re.M);assert external==cfg['external_standard_boundaries'],external
assert cp.read_bytes()==raw
(D/'extraction.json').write_text(json.dumps({'status':'extracted unchanged source; explicit standard primitive model boundaries, no frontend normalization','configuration_sha256':hashlib.sha256(raw).hexdigest(),'commands':commands,'files_sha256':{f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(D.iterdir()) if f.is_file()}},indent=2)+'\n')
print('PASS all40 original FixedInt bodies; two standard external boundaries and six pointer aliases separately modeled')

host=subprocess.check_output(['rustc','-vV'],text=True).split('host: ')[1].splitlines()[0]
for name in ('Types.lean','Funs.lean'):
 if (D/name).read_bytes()!=(R/'aeneas/profiles/default/proofs/Generated'/host/'IntegerFixedDirect'/name).read_bytes():raise ValueError('Fresh fixed model differs: '+name)
