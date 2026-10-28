#!/usr/bin/env python3
"""Register all maintained named proofs and independently reviewed public bindings."""
from pathlib import Path
import argparse,json,re,tomllib
R=Path(__file__).resolve().parents[1];p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();checked=[]
for f in sorted((R/'aeneas/profiles/default/proofs').rglob('*.lean')):
 if '.lake' in f.parts:continue
 s=f.read_text();names=re.findall(r'^\s*(?:@\[[^\]]+\]\s*)?(?:theorem|lemma)\s+([\w.]+)',s,re.M)
 if not names:continue
 ns=re.findall(r'^namespace (\S+)\s*$',s,re.M);assert len(ns)==1,(f,ns)
 module=f.relative_to(R/'aeneas/profiles/default/proofs').with_suffix('').as_posix().replace('/','.')
 for n in names:checked.append({'name':ns[0]+'.'+n,'module':module,'kind':'support'})
assert checked and len({x['name'] for x in checked})==len(checked);byname={x['name']:x for x in checked}
rows=json.loads((R/'aeneas/profiles/default/api-mappings.json').read_text());assert len(rows)==80 and len({x['api'] for x in rows})==80
for m in rows:
 x=byname[m['theorem']];assert x['module']==m['module'];x.update(kind='public-contract',precondition=m['precondition'])
 for field in ('observable','structural_boundary'):
  if field in m:x[field]=m[field]
errors=[]
for ty in ('u8','u16','u32','u64','usize','i8','i16','i32','i64','isize'):
 n=f'IntegerEncodingEncodeErrors.{ty}_too_small';assert byname[n]['module']=='EncodeErrors';byname[n]['kind']='public-error-contract';byname[n]['precondition']='destination length < canonical minimal varint length; extracted debug-assertion profile'
 errors.append({'api':f'<{ty} as integer_encoding::VarInt>::encode_var','theorem':n})
obj={'checked':checked,'recorder_mappings':[{'api':x['api'],'theorem':x['theorem']} for x in rows], 'error_contracts_not_extra_api_instances':errors,'extracted_but_unproved':[f'<{t} as integer_encoding::VarInt>::decode_var' for t in ('u8','u16','u32','u64','usize','i8','i16','i32','i64','isize')], 'scope':'80/90 builtin scalar callable instances; generic/async I/O excluded, standard model and vector dictionary boundaries explicitly reviewed'}
fields=('api','module','theorem','precondition');proofs=[{k:x[k] for k in fields} for x in rows]
tool={'name':'aeneas','version':'be86ab0f1989d04944292b345b24c435be3ad10a','expand_api':True,'lean_dir':'aeneas/profiles/default/proofs','proofs':proofs}
config_path=R/'aeneas/profiles/default/proofs.toml'
current=config_path.read_text();config=tomllib.loads(current)
assert set(config)=={'report','tool'}
headers=list(re.finditer(r'^\[tool\][ \t]*$',current,re.M));assert len(headers)==1
report_prefix=current[:headers[0].start()]
assert tomllib.loads(report_prefix)=={'report':config['report']}
lines=['[tool]']
for k,v in tool.items():
 if k!='proofs':lines.append(k+' = '+json.dumps(v))
lines.append('')
for x in proofs:
 lines.append('[[tool.proofs]]')
 lines.extend(k+' = '+json.dumps(x[k]) for k in fields);lines.append('')
s=report_prefix+'\n'.join(lines);assert tomllib.loads(s)=={'report':config['report'],'tool':tool}
for path,value in [(R/'aeneas/profiles/default/theorems.json',json.dumps(obj,indent=2)+'\n')]:
 if a.check:assert path.read_text()==value,path
 else:path.write_text(value)
if a.check:assert config['tool']==tool,config_path
else:config_path.write_text(s)
print(f'PASS {len(checked)} named proofs;80 unique public mappings;10 extra short-buffer error contracts add no API instances')
