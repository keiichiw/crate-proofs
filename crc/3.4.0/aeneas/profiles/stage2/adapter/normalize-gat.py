#!/usr/bin/env python3

from pathlib import Path as _Path
import os as _os
PROFILE = _Path(__file__).resolve().parents[1]
CRATE = PROFILE.parents[2]
"""Reviewed first-order type lifting plus capture-avoiding local display names of crc Implementation::Data into D."""
import argparse,copy,hashlib,json,pathlib
p=argparse.ArgumentParser();p.add_argument('input');p.add_argument('output');a=p.parse_args()
raw=pathlib.Path(a.input).read_bytes();obj=json.loads(raw);orig=copy.deepcopy(obj);j=obj['translated']
assert not obj['has_errors'];assert j['options']['preset']=='aeneas' or j['options']['preset']=='Aeneas'
assert j['type_decls'][2]['item_meta']['name']==[{'Ident':['crc',0]},{'Ident':['Crc',0]}]
assert j['type_decls'][3]['item_meta']['name']==[{'Ident':['crc',0]},{'Ident':['Digest',0]}]
assert j['trait_decls'][2]['item_meta']['name']==[{'Ident':['crc',0]},{'Ident':['Implementation',0]}]
assert j['trait_decls'][2]['methods']==[] and j['trait_impls'][7]['methods']==[]
assert j['trait_impls'][7]['impl_trait']['id']==2
assert len(j['trait_impls'][7]['generics']['const_generics'])==1
expected_projection=copy.deepcopy(j['type_decls'][2]['kind']['Struct'][1]['ty']['Untagged'])
assert expected_projection['TraitType'][0]['Untagged']['kind']=={'Clause':[{'Free':0},{'regions':[]}]}
assert expected_projection['TraitType'][0]['Untagged']['trait_decl_ref']['id']==2
assert expected_projection['TraitType'][2]==dict(regions=[],types=[{'Untagged':{'TypeVar':{'Free':0}}}],const_generics=[],trait_refs=[])
U=lambda x:{'Untagged':x}
D=U({'TypeVar':{'Free':2}})
G=lambda:dict(regions=[],types=[],const_generics=[],trait_refs=[])
arr_template=copy.deepcopy(j['trait_impls'][7]['types'][0]['skip_binder']['value'])
assert arr_template['Untagged']['Array'][0]['Untagged']['Array'][0]==U({'TypeVar':{'Bound':[0,0]}})
changes={'type_refs':0,'data_fields':0}
def data_for(types,ctx):
 assert len(types)==2
 w,impl=types
 if impl==U({'TypeVar':{'Free':1}}):
  assert ctx in (2,3);return copy.deepcopy(D)
 adt=impl['Untagged']['Adt'];assert adt['id']==1
 g=adt['generics'];assert g['regions']==[] and g['types']==[] and len(g['const_generics'])==1 and g['trait_refs']==[]
 out=copy.deepcopy(arr_template);out['Untagged']['Array'][0]['Untagged']['Array'][0]=copy.deepcopy(w);out['Untagged']['Array'][1]=copy.deepcopy(g['const_generics'][0]);return out
def rewrite(x,ctx=None):
 if isinstance(x,list):return [rewrite(v,ctx) for v in x]
 if not isinstance(x,dict):return x
 # Only a TypeDeclRef (including aggregate/place type references), not arbitrary IDs.
 if set(x)=={'id','generics','builtin'} and x['id'] in (2,3):
  out=copy.deepcopy(x);g=out['generics'];assert len(g['types'])==2 and len(g['trait_refs'])==1, x
  assert g['trait_refs'][0]['skip_binder']['Untagged']['trait_decl_ref']['id']==2
  data=data_for(g['types'],ctx);g['types'].append(data);g['trait_refs']=[];changes['type_refs']+=1
  return {k:rewrite(v,ctx) for k,v in out.items()}
 if 'TraitType' in x:
  assert ctx==2 and x==expected_projection;changes['data_fields']+=1;return copy.deepcopy(D['Untagged'])
 return {k:(v if k=='item_meta' else rewrite(v,ctx)) for k,v in x.items()}
for field,values in list(j.items()):
 if field=='type_decls':
  for i,t in enumerate(values):
   if t is not None:values[i]=rewrite(t,i if i in (2,3) else None)
 elif field not in ('trait_decls','trait_impls','item_names','assoc_item_names','short_names'):j[field]=rewrite(values)
for i,t in enumerate(j['trait_decls']):
 if t is not None and i!=2:j['trait_decls'][i]=rewrite(t)
for i,t in enumerate(j['trait_impls']):
 if t is not None and i!=7:j['trait_impls'][i]=rewrite(t)
for i in (2,3):
 t=j['type_decls'][i];g=t['generics'];assert len(g['trait_clauses'])==1 and g['trait_clauses'][0]['trait_']['skip_binder']['id']==2
 g['trait_clauses']=[];g['types'].append({'index':2,'name':'D','variance':'Invariant'})
j['trait_decls'][2]=None;j['trait_impls'][7]=None
# Remove only their declaration-order entries; all function declarations retained.
def retained(e):
 for kind,idx in [('TraitDecl',2),('TraitImpl',7)]:
  if kind in e:
   d=e[kind]
   if d=={'NonRec':idx}:return False
   if 'Rec'in d:
    assert idx not in d['Rec']
 return True
j['ordered_decls']=[e for e in j['ordered_decls'] if retained(e)]
assert len(j['fun_decls'])==len(orig['translated']['fun_decls'])
accepted_changes=copy.deepcopy(changes)
for f0,f1 in zip(orig['translated']['fun_decls'],j['fun_decls']):
 if f0 is not None:assert rewrite(f0)==f1
alpha=[]
for f in j['fun_decls']:
 if f is None:continue
 name=f['item_meta']['name']
 if name[:2]!=[{'Ident':['crc',0]},{'Ident':['table',0]}]:continue
 body=f['body']
 if 'Structured' not in body:continue
 assert all(v['name']!='lookup_table' for v in body['Structured']['locals']['locals'])
 for local in body['Structured']['locals']['locals']:
  if local['name']=='table':
   alpha.append({'function':f['def_id'],'local':local['index'],'old':'table','new':'lookup_table'})
   local['name']='lookup_table'
out=pathlib.Path(a.output);out.write_text(json.dumps(obj,separators=(',',':'))+'\n')
(out.with_suffix('.normalization.json')).write_text(json.dumps({'input_sha256':hashlib.sha256(raw).hexdigest(),'output_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'changes':accepted_changes,'display_name_renames':alpha,'function_declarations_retained':len(j['fun_decls']),'rule':'add first-order D=[[W;256];L] to Crc/Digest; methodless GAT metadata erased'},indent=2)+'\n')
