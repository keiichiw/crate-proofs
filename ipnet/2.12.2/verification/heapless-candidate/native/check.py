#!/usr/bin/env python3
"""Finite native checks only; not a formal proof of all inputs."""
import hashlib,json,pathlib,subprocess,tempfile
root=pathlib.Path(__file__).resolve().parent
run=pathlib.Path(tempfile.mkdtemp(prefix='check-',dir=root.parent/'runs'))
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
inputs={str(p.relative_to(root.parent)):digest(p) for p in [root/'Cargo.toml',root/'Cargo.lock',root/'src/main.rs',pathlib.Path(__file__),root.parent/'Cargo.toml',root.parent/'Cargo.lock',*sorted((root.parent/'src').glob('*.rs'))]}
results=[]
for std in [True,False]:
 for feature in ['heapless','heapless,serde-only','legacy','heapless,legacy','serde-only']:
  cmd=['cargo','+1.91.1','run','--offline','--locked','--manifest-path',str(root/'Cargo.toml')]
  if not std: cmd+=['--no-default-features']
  cmd+=['--features',feature]
  p=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  name=('std' if std else 'no-default')+'-'+feature.replace(',','_')+'.log'
  (run/name).write_text(p.stdout)
  results.append(dict(command=cmd,exit_code=p.returncode,log=name,sha256=digest(run/name)))
  print(name,p.returncode,flush=True)
  if p.returncode: break
result=dict(kind='finite-native-only',cases_per_run=6216,inputs=inputs,results=results)
(run/'native-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(run,flush=True)
raise SystemExit(any(r['exit_code'] for r in results))
