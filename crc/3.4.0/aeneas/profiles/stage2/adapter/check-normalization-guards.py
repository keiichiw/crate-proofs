#!/usr/bin/env python3

from pathlib import Path as _Path
import os as _os
PROFILE = _Path(__file__).resolve().parents[1]
CRATE = PROFILE.parents[2]
"""Negative evidence: reject schema/body/type/display changes beyond the reviewed adapter."""
from pathlib import Path
import argparse,copy,hashlib,json,subprocess,sys
p=argparse.ArgumentParser();p.add_argument('original');p.add_argument('normalized');p.add_argument('--output',required=True);a=p.parse_args();D=Path(a.output).resolve();D.mkdir(parents=True,exist_ok=False)
R=PROFILE;n=json.loads(Path(a.normalized).read_bytes());rows=[]
def extra(x):x['unreviewed_schema_key']=True
def argc(x):
 f=next(f for f in x['translated']['fun_decls'] if f and f['item_meta']['is_local'] and f['body']);f['body']['Structured']['locals']['arg_count']+=1
def display(x):
 f=next(f for f in x['translated']['fun_decls'] if f and isinstance(f['body'],dict) and 'Structured' in f['body'] and any(z['name']=='algorithm' for z in f['body']['Structured']['locals']['locals']));z=next(z for z in f['body']['Structured']['locals']['locals'] if z['name']=='algorithm');z['name']='lookup_table'
def dtype(x):
 g=x['translated']['type_decls'][2]['generics'];g['types'][2]['variance']='Bivariant'
def projection(x):x['translated']['type_decls'][2]['kind']['Struct'][1]['ty']={'Untagged':{'TypeVar':{'Free':0}}}
for name,mutate in [('extra-schema',extra),('argument-count',argc),('unapproved-local-name',display),('type-variance',dtype),('wrong-data-projection',projection)]:
 x=copy.deepcopy(n);mutate(x);f=D/'invalid-input.llbc';f.write_text(json.dumps(x,separators=(',',':'))+'\n');h=hashlib.sha256(f.read_bytes()).hexdigest()
 c=[sys.executable,str(R/'adapter/check-normalization.py'),a.original,str(f),'--output',str(D/'must-not-pass.json')]
 r=subprocess.run(c,capture_output=True,text=True);log=r.stdout+r.stderr;(D/(name+'.log')).write_text(log)
 assert r.returncode!=0 and 'AssertionError' in log,name
 rows.append({'case':name,'invalid_input_sha256':h,'status':'rejected','exit':r.returncode})
 f.unlink()
assert not (D/'must-not-pass.json').exists()
(D/'result.json').write_text(json.dumps({'status':'passed','cases':rows},indent=2)+'\n');print('PASS five independent rejection guards')
