#!/usr/bin/env python3

from pathlib import Path as _Path
import os as _os
PROFILE = _Path(__file__).resolve().parents[1]
CRATE = PROFILE.parents[2]
"""Register every maintained named theorem and explicit reviewed API mappings."""
from pathlib import Path
import argparse,json,re,tomllib
R=PROFILE
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
checked=[];modules=[]
for f in sorted((R/'proofs/Stage2Proofs').glob('*.lean')):
 s=f.read_text();ns=re.findall(r'^namespace (\S+)\s*$',s,re.M)
 assert len(ns)==1,(f,ns)
 names=re.findall(r'^\s*(?:@\[[^\]]+\]\s*)?(?:theorem|lemma)\s+([\w.]+)',s,re.M)
 assert len(names)==len(re.findall(r'\b(?:theorem|lemma)\s+[\w.]+',s)),f
 module='Stage2Proofs.'+f.stem;modules.append(module)
 for name in names:checked.append({'name':ns[0]+'.'+name,'module':module,'kind':'support'})
assert len({x['name'] for x in checked})==len(checked)
byname={x['name']:x for x in checked}
mappings=json.loads((R/'config/api-mappings.json').read_text())
assert len({x['api'] for x in mappings})==len(mappings)
for m in mappings:
 x=byname[m['theorem']];assert x['module']==m['module'],m
 assert 'precondition' not in x or x['precondition']==m['precondition'],m
 x.update(kind='public-contract',precondition=m['precondition'])
obj={'checked':checked,'recorder_mappings':[{'api':x['api'],'theorem':x['theorem']} for x in mappings],
 'scope':'actual canonical checksum/update under explicit valid-domain/state invariants; separate public word-level endpoints, full-width constructors and supporting lemmas; optimized 16-lane message computation excluded'}
report_path=R/'proofs.toml'
report_text=report_path.read_text()
report={'report':tomllib.loads(report_text)['report'],
 'tool':{'name':'aeneas','version':'be86ab0f1989d04944292b345b24c435be3ad10a','lean_dir':'.work/selected-proofs','proofs':mappings}}
# JSON strings are valid TOML basic strings for the present ASCII field values.
# Preserve independently reviewed editorial prose when regenerating mappings.
for header in re.finditer(r'^\[\s*tool\s*\][ \t]*(?:#.*)?$',report_text,re.M):
 try:prefix=tomllib.loads(report_text[:header.start()])
 except tomllib.TOMLDecodeError:continue # A literal header inside multiline prose.
 if prefix=={'report':report['report']}:
  report_prefix=report_text[:header.start()]
  break
else:raise ValueError('Missing top-level tool table')
lines=[]
for section in ('tool',):
 lines.append('['+section+']')
 for k,v in report[section].items():
  if k!='proofs':lines.append(k+' = '+json.dumps(v))
 lines.append('')
for m in mappings:
 lines.append('[[tool.proofs]]')
 for k in ('api','module','theorem','precondition'):lines.append(k+' = '+json.dumps(m[k]))
 lines.append('')
outputs={R/'theorems.json':json.dumps(obj,indent=2)+'\n',R/'proofs.toml':report_prefix+'\n'.join(lines),
 R/'proofs/Stage2Proofs.lean':''.join('import '+m+'\n' for m in modules)}
assert tomllib.loads(outputs[R/'proofs.toml'])==report
for path,value in outputs.items():
 if a.check:
  if path==report_path:assert tomllib.loads(path.read_text())==report,path
  else:assert path.read_text()==value,path
 else:path.write_text(value)
print(f'PASS {len(checked)} named theorems, {len(modules)} modules, {len(mappings)} explicit public mappings')
