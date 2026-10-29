#!/usr/bin/env python3

from pathlib import Path as _Path
import os as _os
PROFILE = _Path(__file__).resolve().parents[1]
CRATE = PROFILE.parents[2]
"""Check source inventory and explicit formal mappings without counting helpers as APIs."""
from pathlib import Path
import json,re
R=PROFILE
public=['new','checksum','digest','digest_with_initial','table','update','finalize']
for n in (8,16,32,64,128):
 s=(CRATE/f'.work/source/src/crc{n}.rs').read_text()
 assert re.findall(r'pub const fn (\w+)',s)==public,n
s=(CRATE/'.work/source/src/lib.rs').read_text()
assert s.count('#[derive(Clone)]')==2 and '#[derive(Copy, Clone)]' in s
expected={f'Crc<u{n}, Table<{l}>>::table':f'CrcProofs.table_u{n}_l{l}_spec' for n in (8,16,32,64,128) for l in (0,1,16)}
for l in (0,1,16):
 expected[f'Table<{l}>::clone']=f'CrcProofs.table_clone_l{l}_spec'
 expected[f'Table<{l}>::clone_from']=f'CrcProofs.table_clone_from_l{l}_spec'
i=json.loads((R/'theorems.json').read_text())
assert {x['api']:x['theorem'] for x in i['recorder_mappings']}==expected
byname={x['name']:x for x in i['checked']}
for t in expected.values():assert byname[t]['precondition']=='true'
for n in (8,16,32,64,128):assert f'crc.crc{n}_polynomial_spec' in byname
c=json.loads((R/'config/coverage.json').read_text())
assert c['supported_callable_instances']==171 and c['formal_public_instances']==len(expected)==21
assert c['formal_inherent_instances']==15 and c['inherent_instances']==105
assert c['formal_crc_checksum_instances']==0
assert c['private_kernel_widths']==[8,16,32,64,128]
print('PASS public21/171 (supported built-in instances); inherent15/105; checksum0/15; private kernels5 counted separately')
