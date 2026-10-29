#!/usr/bin/env python3

from pathlib import Path as _Path
import os as _os
PROFILE = _Path(__file__).resolve().parents[1]
CRATE = PROFILE.parents[2]
"""Independent structural checker: exact operations, specified types and display-name alpha-renaming.
Does not import or execute the normalizer and does not prove compiler correctness.
"""
import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('original');p.add_argument('normalized');p.add_argument('--output',required=True);a=p.parse_args()
O=json.loads(Path(a.original).read_bytes());N=json.loads(Path(a.normalized).read_bytes());o=O['translated'];n=N['translated'];count=0;alpha=[]
assert set(O)==set(N) and set(o)==set(n)
assert not O['has_errors'] and not N['has_errors']
U=lambda v:{'Untagged':v}
D=U({'TypeVar':{'Free':2}})
us=U({'Scalar':{'Integer':{'Unsigned':'Usize'}}})
size256=U([{'Integer':{'Unsigned':['Usize','256']}},us])
def expected_data(ts,ctx):
 w,i=ts
 if i==U({'TypeVar':{'Free':1}}):assert ctx in (2,3);return D
 d=i['Untagged']['Adt'];assert d['id']==1 and d['builtin'] is None
 g=d['generics'];assert g['types']==[] and g['regions']==[] and g['trait_refs']==[] and len(g['const_generics'])==1
 return U({'Array':[U({'Array':[w,size256,None]}),g['const_generics'][0],None]})
def check(x,y,path='',ctx=None):
 global count
 if isinstance(x,str) and x=='table' and y=='lookup_table':
  match=re.fullmatch(r'fun_decls/(\d+)/body/Structured/locals/locals/(\d+)/name',path)
  if match:
   fi,li=map(int,match.groups());f=o['fun_decls'][fi]
   ident=[c['Ident'][0] for c in f['item_meta']['name'] if 'Ident' in c]
   assert ident[:2]==['crc','table'],path
   assert 'lookup_table' not in [z['name'] for z in f['body']['Structured']['locals']['locals']],path
   alpha.append([fi,li]);return
 if ctx==2 and x==o['type_decls'][2]['kind']['Struct'][1]['ty']:
  assert y==D,(path,'exact Data<W> projection substitution');return
 if isinstance(x,dict) and set(x)=={'id','generics','builtin'} and x['id'] in (2,3):
  assert isinstance(y,dict) and set(y)==set(x) and y['id']==x['id'] and y['builtin']==x['builtin'],path
  g=x['generics'];h=y['generics'];assert set(g)==set(h),path
  assert len(g['types'])==2 and len(h['types'])==3 and len(g['trait_refs'])==1 and h['trait_refs']==[],path
  assert g['trait_refs'][0]['skip_binder']['Untagged']['trait_decl_ref']['id']==2,path
  assert h['types'][2]==expected_data(g['types'],ctx),(path,'data type')
  for k in g:
   if k=='types':check(g[k],h[k][:2],path+'/types',ctx)
   elif k!='trait_refs':check(g[k],h[k],path+'/'+k,ctx)
  count+=1;return
 if isinstance(x,dict):
  assert isinstance(y,dict) and set(x)==set(y),(path,'dict keys')
  for k in x:
   if k in ('item_meta','item_names','assoc_item_names','short_names'):assert x[k]==y[k],path+'/'+k
   else:check(x[k],y[k],path+'/'+k,ctx)
 elif isinstance(x,list):
  assert isinstance(y,list) and len(x)==len(y),(path,'list length')
  for i,(v,w) in enumerate(zip(x,y)):check(v,w,path+'/'+str(i),ctx)
 else:assert x==y,(path,x,y)
# Every complete function including metadata, locals, constants, calls, branches and loops.
check(o['fun_decls'],n['fun_decls'],'fun_decls')
assert len(o['fun_decls'])==len(n['fun_decls'])
# Type layout changes must be exactly the two structural representation lifts.
assert len(o['type_decls'])==len(n['type_decls'])
for i,(x,y) in enumerate(zip(o['type_decls'],n['type_decls'])):
 if i not in (2,3):check(x,y,'types/'+str(i));continue
 assert set(x)==set(y)
 assert x['item_meta']==y['item_meta'] and x['def_id']==y['def_id'] and x['src']==y['src']
 assert set(x['kind'])==set(y['kind'])=={'Struct'}
 for k in x:
  if k not in ('item_meta','def_id','src','generics','kind'):check(x[k],y[k],'type-extra/'+str(i)+'/'+k,i)
 gx=x['generics'];gy=y['generics'];assert set(gx)==set(gy);assert len(gx['types'])==2 and gy['types']==gx['types']+[{'index':2,'name':'D','variance':'Invariant'}]
 assert len(gx['trait_clauses'])==1 and gx['trait_clauses'][0]['trait_']['skip_binder']['id']==2 and gy['trait_clauses']==[]
 for k in gx:
  if k not in ('types','trait_clauses'):check(gx[k],gy[k],'type-generics/'+str(i)+'/'+k)
 fx=x['kind']['Struct'];fy=y['kind']['Struct'];assert len(fx)==len(fy)==2
 for j,(b,c) in enumerate(zip(fx,fy)):
  if i==2 and j==1:
   assert b['name']=='data' and c['name']=='data' and c['ty']==D
   assert 'TraitType' in b['ty']['Untagged']
   check({k:v for k,v in b.items() if k!='ty'},{k:v for k,v in c.items() if k!='ty'},'Crc/data-metadata')
  else:check(b,c,'type-field/'+str(i)+'/'+str(j),i)
# Exactly methodless Implementation trait/implementation declarations are dropped.
for key,idx in [('trait_decls',2),('trait_impls',7)]:
 assert len(o[key])==len(n[key]) and o[key][idx]['methods']==[] and n[key][idx] is None
 for i,(x,y) in enumerate(zip(o[key],n[key])):
  if i!=idx:check(x,y,key+'/'+str(i))
old_order=o['ordered_decls'];new_order=[e for e in old_order if e not in ({'TraitDecl':{'NonRec':2}},{'TraitImpl':{'NonRec':7}})]
assert n['ordered_decls']==new_order and len(old_order)-len(new_order)==2
for key in o:
 if key in ('item_names','assoc_item_names','short_names'):assert o[key]==n[key]
 elif key not in ('fun_decls','type_decls','trait_decls','trait_impls','ordered_decls'):check(o[key],n[key],key)
for key in O:
 if key!='translated':check(O[key],N[key],key)
def no_gat(v):
 if isinstance(v,list):
  for x in v:no_gat(x)
 elif isinstance(v,dict):
  assert 'TraitType' not in v,'unresolved associated type'
  if 'trait_decl_ref' in v:assert v['trait_decl_ref']['id']!=2
  if 'TraitImpl' in v:
   q=v['TraitImpl']
   if 'id' in q:assert q['id']!=7
   elif 'NonRec' in q:assert q['NonRec']!=7
   elif 'Rec' in q:assert 7 not in q['Rec']
   else:assert q['impl_ref']['id']!=7 and q['trait_ref']['id']!=2
  for k,x in v.items():
   if k not in ('item_meta','item_names','assoc_item_names','short_names'):no_gat(x)
no_gat(n)
expected_alpha=[]
for fi,f in enumerate(o['fun_decls']):
 if f and isinstance(f['body'],dict) and [c['Ident'][0] for c in f['item_meta']['name'] if 'Ident' in c][:2]==['crc','table']:
  for li,local in enumerate(f['body']['Structured']['locals']['locals']):
   if local['name']=='table':expected_alpha.append([fi,li])
assert alpha==expected_alpha and len(alpha)==5,'missing or extra display-name normalization'
report={'status':'passed','scope':'independent exact AST comparison modulo storage type lift and checked local display alpha-renaming; not a verified compiler','functions_exact_modulo_type_correspondence':sum(f is not None for f in o['fun_decls']),'checked_type_references':count,'local_display_alpha_renames':alpha,'input_sha256':hashlib.sha256(Path(a.original).read_bytes()).hexdigest(),'normalized_sha256':hashlib.sha256(Path(a.normalized).read_bytes()).hexdigest()}
Path(a.output).write_text(json.dumps(report,indent=2)+'\n');print(report)
