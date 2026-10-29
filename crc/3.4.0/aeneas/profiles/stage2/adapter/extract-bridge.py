#!/usr/bin/env python3

from source_coordinates import canonicalize
from pathlib import Path as _Path
import os as _os
PROFILE = _Path(__file__).resolve().parents[1]
CRATE = PROFILE.parents[2]
"""Fresh source-backed init/finalize extraction with explicit standard primitive boundary."""
from pathlib import Path
import argparse,hashlib,json,subprocess,re
R=PROFILE;V=CRATE
p=argparse.ArgumentParser();p.add_argument('--output',required=True,type=Path);a=p.parse_args();D=a.output.resolve();D.mkdir(parents=True,exist_ok=False)
entries=[f'crate::crc{n}::{name}' for n in (8,16,32,64,128) for name in ('init','finalize')]
cmd=['charon','cargo','--rustc-arg=--remap-path-prefix='+str(CRATE)+'=crc-3.4.0','--preset=aeneas',*[z for e in entries for z in ('--start-from',e)],'--opaque','crate',*[z for e in entries for z in ('--include',e)],'--include','core::num::_::reverse_bits','--remove-unused-clauses','--dest-file',str(D/'crc_stage2.llbc'),'--','--lib','--locked']
cmd2=['aeneas','-backend','lean','-split-files','-namespace','CrcStage2','-dest',str(D),str(D/'crc_stage2.llbc')]
for label,c in [('charon',cmd),('aeneas',cmd2)]:
 with (D/(label+'.log')).open('w') as f:subprocess.run(c,cwd=V,stdout=f,stderr=subprocess.STDOUT,check=True)
 if label=='charon':canonicalize(D/'crc_stage2.llbc',CRATE,V)
assert {f.name for f in D.glob('*.lean')}=={'Types.lean','Funs.lean','FunsExternal_Template.lean'}
for name in ('Types.lean','Funs.lean'):
 s=(D/name).read_text();assert not re.search(r'(?m)^\s*(?:axiom|opaque|partial\s+def)\b|\b(?:sorry|admit)\b',s)
s=(D/'FunsExternal_Template.lean').read_text()
assert re.findall(r'^axiom (\S+)',s,re.M)==['core.intrinsics.bitreverse']
for n in (8,16,32,64,128):
 for name in ('init','finalize'):assert f'def crc{n}.{name}' in (D/'Funs.lean').read_text()
(D/'extraction.json').write_text(json.dumps({'commands':[cmd,cmd2],'standard_primitive':'core.intrinsics.bitreverse: unsigned8/16/32/64/128 only; authored explicit semantics, not an application axiom','files_sha256':{f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(D.iterdir()) if f.is_file()}},indent=2)+'\n')
print('PASS fresh bridge source models; sole declared standardprimitive boundary checked')
