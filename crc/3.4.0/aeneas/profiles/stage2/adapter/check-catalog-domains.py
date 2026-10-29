#!/usr/bin/env python3

from pathlib import Path as _Path
import os as _os
PROFILE = _Path(__file__).resolve().parents[1]
CRATE = PROFILE.parents[2]
"""Measure source parameter domains; this is not a formal check-value proof."""
from pathlib import Path
import argparse,collections,hashlib,json,re,tarfile
p=argparse.ArgumentParser();p.add_argument('--output',required=True);a=p.parse_args();R=PROFILE;V=CRATE;archive=_Path(_os.environ['CRC_CATALOG_ARCHIVE'])
with tarfile.open(archive) as t:s=t.extractfile('crc-catalog-2.5.0/src/algorithm.rs').read().decode()
blocks=re.findall(r'pub const (\w+): Algorithm<u(\d+)> = Algorithm\s*\{(.*?)\};',s,re.S)
rows=[];fields={'width','poly','init','refin','refout','xorout','check','residue'}
for name,n,b in blocks:
 parts=b.strip().rstrip(',').split(',')
 pairs=[]
 for part in parts:
  m=re.fullmatch(r'\s*(\w+):\s*(0x[0-9A-Fa-f_]+|\d+|true|false)\s*',part)
  assert m is not None,(name,part)
  pairs.append(m.groups())
 assert len(pairs)==len(fields) and {k for k,v in pairs}==fields,name
 vals={k:(v=='true' if v in ('true','false') else int(v.replace('_',''),0)) for k,v in pairs};N=int(n);w=vals['width']
 assert N in (8,16,32,64,128) and 1<=w<=N,name
 assert all(0<=vals[k]<(1<<w) for k in ('poly','init','xorout')),name
 assert all(0<=vals[k]<(1<<N) for k in ('check','residue')),name
 rows.append({'name':name,'storage_width':N,**vals,'full_storage_width':w==N})
assert len(rows)==113 and len({x['name'] for x in rows})==113
counts=lambda xs:dict(sorted(collections.Counter(str(x['storage_width']) for x in xs).items(),key=lambda z:int(z[0])))
out={'kind':'source-parameter-domain inventory; not a new formal theorem or check-value proof','archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'catalog_total':len(rows),'valid_width_parameter_cases':len(rows),'full_storage_width_cases':sum(x['full_storage_width'] for x in rows),'smaller_width_cases':sum(not x['full_storage_width'] for x in rows),'storage_counts':counts(rows),'full_storage_counts':counts(x for x in rows if x['full_storage_width']),'algorithms':rows}
Path(a.output).write_text(json.dumps(out,indent=2)+'\n');print('PASS113 valid catalog parameter domains;70 full-storage-width,43 narrower; counts not extra proof coverage')
