#!/usr/bin/env python3

from pathlib import Path as _Path
import os as _os
PROFILE = _Path(__file__).resolve().parents[1]
CRATE = PROFILE.parents[2]
"""Count unique reviewed callable instances, separately from their parameter scope."""
from pathlib import Path
import argparse,json
R=PROFILE;p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
old=json.loads((R.parent/'default/theorems.json').read_text())['recorder_mappings']
new=json.loads((R/'config/api-mappings.json').read_text())
assert len(old)==21
bindings={}
for stage,ms in [('stage1',old),('stage2',new)]:
 for x in ms:
  assert x['api'] not in bindings,x
  bindings[x['api']]={'stage':stage,**x}
rows=[]
for n in (8,16,32,64,128):
 for l in (0,1,16):
  for owner,methods in [('Crc',('new','checksum','digest','digest_with_initial','table','clone','clone_from')),('Digest',('update','finalize','clone','clone_from'))]:
   for method in methods:
    api=f'{owner}<u{n}, Table<{l}>>::{method}'
    row={'api':api,'storage_width':n,'lanes':l,'method':method,'formal':api in bindings}
    if api in bindings:
     row.update(bindings[api])
     row['contract_kind']=('canonical-message' if method in ('checksum','update') else 'word-endpoint' if method in ('digest','digest_with_initial','finalize') else 'constructor' if method=='new' else 'exact-projection-or-clone')
    else:row['limitation']=('optimized sixteen-lane canonical message proof absent' if method in ('checksum','update') and l==16 else 'no accepted public contract')
    rows.append(row)
for l in (0,1,16):
 for method in ('clone','clone_from'):
  api=f'Table<{l}>::{method}';rows.append({'api':api,'lanes':l,'method':method,'formal':True,'contract_kind':'exact-projection-or-clone',**bindings[api]})
assert len(rows)==171 and len({x['api'] for x in rows})==171
assert set(bindings)<=set(x['api'] for x in rows)
msg=[x for x in rows if x.get('contract_kind')=='canonical-message']
assert len(msg)==20 and {x['lanes'] for x in msg}=={0,1}
out={'denominator':'171 supported built-in callable instances for five widths and lanes0/1/16, including explicitly counted Clone::clone_from; excludes reexports, blanket methods and custom generic implementations',
 'supported_callable_instances':171,'formal_public_instances':len(bindings),'formal_public_percent':100*len(bindings)/171,
 'baseline_contract_instances':21,'stage2_contract_instances':len(new),
 'canonical_checksum_instances':sum(x['method']=='checksum' for x in msg),'checksum_instances':15,
 'canonical_digest_update_instances':sum(x['method']=='update' for x in msg),'digest_update_instances':15,
 'canonical_message_domain':'all valid CRC widths 1..storage width, both flags, bounded current polynomial, canonical encoded incoming state; checksum additionally bounded xorout (Table1 u8/u16 roots also require bounded init); Table1 current table coherence required; arbitrary representable slices including empty',
 'word_endpoint_instances':45,'word_endpoint_warning':'word-level init/finalize contracts cover lanes16 but do not prove its message computation',
 'constructor_warning':'each constructor mapping has its own explicit domain; current table coherence must still hold after any algorithm-field replacement',
 'catalog_parameter_domains':{'eligible':113,'meaning':'source constants satisfy the bounded parameter domain; inventory is not 113 independent formal check-value proofs or partial-width constructor proofs'},
 'native_callable_instances':171,'rows':rows}
path=R/'config/coverage.json';s=json.dumps(out,indent=2)+'\n'
if a.check:assert path.read_text()==s
else:path.write_text(s)
print(f'PASS {len(bindings)}/171 distinct supported public contracts; canonical checksum10/15 and update10/15, parameter/state preconditions explicit')
