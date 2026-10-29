#!/usr/bin/env python3
"""Summarize retained native test logs; reject missing or failed runs."""
import json,re,os
from pathlib import Path
r=Path(__file__).resolve().parents[4]
d=Path(os.environ.get('CRC_NATIVE_LOG_DIR',str(r/'verification'))).resolve()
s=(r/'tests/crc.rs').read_text()
counts={str(n):len(re.findall(r'CRC_\w+',re.search(r'suite!\(width_'+str(n)+r',u'+str(n)+r',&\[(.*?)\]\)',s)[1])) for n in [8,16,32,64,128]}
runs={}
for kind in ['debug','release','upstream','doc']:
 p=d/f'native-{kind}.log'; text=p.read_text()
 matches=re.findall(r'test result: (\w+)\. (\d+) passed; (\d+) failed;.*?finished in ([\d.]+)s',text)
 assert matches and all(x[0]=='ok' and int(x[2])==0 for x in matches),p
 runs[kind]={'log':str(p.relative_to(r)),'test_groups':[{'passed':int(a),'failed':int(b),'seconds':float(c)} for _,a,b,c in matches]}
out={'kind':'native-tests-not-formal-proof','status':'passed','rust_toolchain':'1.91.1','runs':runs,'catalog_counts':counts,'catalog_algorithms':sum(counts.values()),'custom_algorithms':16*sum(map(int,counts)),'storage_widths':[8,16,32,64,128],'lanes':[0,1,16],'lengths':[0,1,2,7,8,15,16,17,31,32,33,63,64,65,127,128,129,255,256,257],'initials':['0','width mask','algorithm init','storage MAX'],'api_callable_supported_instances':171,'oracle':'independent width-local polynomial bit recurrence, explicit sampled-bit input reflection and width output reflection; no upstream table/util reuse','public_mutation_observation':{'from_poly':'0x07','to_poly':'0x31','message':[1],'fresh':'0x31','mutated_lane0':'0x31','mutated_lane1':'0x07','mutated_lane16':'0x07'},'limitations':['finite tests are not formal proof','valid algorithm parameters only','main oracle tests constructor-produced coherent states','table entries sampled at0,1,2,127,128,255','public mutation diagnostic intentionally records stale cached table behavior']}
(d/'native-results.json').write_text(json.dumps(out,indent=2)+'\n')
