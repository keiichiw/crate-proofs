#!/usr/bin/env python3
"""Reproduce known counterexamples; exit zero means the bug was reproduced."""
import hashlib,json,os,pathlib,subprocess,sys,tempfile
root=pathlib.Path(__file__).resolve().parent
version=root.parents[2]
evidence=[]
target=pathlib.Path(tempfile.mkdtemp(prefix='issue-repros-',dir=version/'verification/runs'))/'target'
env=os.environ.copy(); env['CARGO_TARGET_DIR']=str(target)
def run(name,cmd,stdin=None):
 p=subprocess.run([str(x) for x in cmd],input=stdin,stdout=subprocess.PIPE,stderr=subprocess.PIPE,env=env)
 (root/(name+'.stdout')).write_bytes(p.stdout)
 (root/(name+'.stderr')).write_bytes(p.stderr)
 evidence.append(dict(name=name,command=[str(x) for x in cmd],exit_code=p.returncode))
 print(name,p.returncode,flush=True)
 if p.returncode: raise SystemExit(p.returncode)
 return p.stdout
output=run('schema',['cargo','+1.91.1','run','--offline','--locked','--manifest-path',root/'Cargo.toml'])
run('schema-check',[version/'.tools/schema-python/bin/python',root/'schema-minimal.py'],output)
for binary in ['ipnet-heapless-feature-repro','ipv6']:
 for feature in ['heapless','legacy']:
  args=['cargo','+1.91.1','run','--offline','--locked','--manifest-path',version/'verification/bugs/heapless-feature-repro/Cargo.toml','--features',feature]
  if binary=='ipv6': args+=['--bin','ipv6']
  run(binary+'-'+feature,args)
files=[root/'run.py',root/'Cargo.toml',root/'Cargo.lock',root/'schema-minimal.rs',root/'schema-minimal.py',*root.glob('*.stdout'),*root.glob('*.stderr')]
files+=list((version/'verification/bugs/heapless-feature-repro/src').rglob('*.rs'))
files += [version/'verification/bugs/heapless-feature-repro'/n for n in ['Cargo.toml','Cargo.lock']]
(root/'evidence.json').write_text(json.dumps({'checks':evidence,'fresh_target':target.parent.name,'sha256':{str(p.relative_to(version)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}},indent=2)+'\n')
