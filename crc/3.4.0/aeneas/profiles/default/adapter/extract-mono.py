#!/usr/bin/env python3

from source_coordinates import canonicalize
from pathlib import Path as _Path
import os as _os
PROFILE = _Path(__file__).resolve().parents[1]
CRATE = PROFILE.parents[2]
"""Extract concrete upstream table bodies via call-only monomorphization anchors."""
import argparse, hashlib, json, os, pathlib, re, subprocess
p=argparse.ArgumentParser();p.add_argument('--output',required=True);p.add_argument('--config',default=None);args=p.parse_args()
r=CRATE;config=pathlib.Path(args.config).resolve() if args.config else PROFILE/'config/mono.json';raw=config.read_bytes();cfg=json.loads(raw)
if any(not re.fullmatch(r'crate::(?:table_u(?:8|16|32|64|128)_l(?:0|1|16)|table_clone_l(?:0|1|16)|table_clone_from_l(?:0|1|16))',e) for e in cfg['entries']): raise ValueError('unreviewed anchor entry')
out=pathlib.Path(args.output).resolve();out.mkdir(parents=True,exist_ok=False)
harness=PROFILE/'capture/mono-harness'
env=os.environ.copy();env['CARGO_TARGET_DIR']=_os.environ['CARGO_TARGET_DIR']
extra=cfg.get('dependency_include',[])
if extra not in ([],['core::clone::Clone::clone_from']):raise ValueError('unreviewed dependency')
namespace=cfg.get('namespace')
if namespace is not None and namespace not in ['TableCloneFrom0','TableCloneFrom1','TableCloneFrom16']:raise ValueError('unreviewed namespace')
commands=[['charon','cargo','--rustc-arg=--remap-path-prefix='+str(CRATE)+'=crc-3.4.0','--preset=aeneas','--monomorphize',*[x for e in cfg['entries'] for x in ['--start-from',e]],'--include','crc',*[x for e in extra for x in ['--include',e]],'--dest-file',str(out/'anchors.llbc'),'--','--lib','--locked'],['aeneas','-backend','lean',*(['-namespace',namespace] if namespace else []),'-dest',str(out),str(out/'anchors.llbc')]]
for label,cmd in zip(['charon','aeneas'],commands):
 with (out/f'{label}.log').open('w') as log:subprocess.run(cmd,cwd=harness,stdout=log,stderr=subprocess.STDOUT,check=True,env=env)
 if label=='charon':canonicalize(out/'anchors.llbc',CRATE,harness)
actual={p.name for p in out.glob('*.lean')}
if actual!=set(cfg['models']):raise ValueError(f'inventory mismatch {actual}')
for f,names in cfg['models'].items():
 s=(out/f).read_text()
 if re.search(r'(?m)^\s*(?:axiom|opaque|partial\s+def)\b|\b(?:sorry|admit)\b',s):raise ValueError('incomplete model')
 for n in names:
  match = re.search(rf'(?m)^def {re.escape(n)}(?=\s|\(|:)',s)
  if not match:raise ValueError(f'missing actual body {n}')
  doc = s[:match.start()].rsplit('/--',1)[-1]
  if 'crc-source/src' not in doc and ('core.clone.Clone.clone_from.default' != n or '/rustc/library/core/src/clone.rs' not in doc):raise ValueError(f'body lacks upstream span: {n}')

if config.read_bytes()!=raw:raise ValueError('config changed')
(out/'extraction.json').write_text(json.dumps({'status':'extracted-not-proved','commands':commands,'config_sha256':hashlib.sha256(raw).hexdigest(),'files_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in out.iterdir() if p.is_file()}},indent=2)+'\n')
print(f'Extracted (not proved): {out}')
