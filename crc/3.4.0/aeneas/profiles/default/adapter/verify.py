#!/usr/bin/env python3
"""CRC-specific extraction, finite oracles, structural guards and coverage checks."""
from pathlib import Path
import argparse, hashlib, json, os, platform, shutil, subprocess, tarfile, tomllib, urllib.request
if not __debug__:raise RuntimeError('CRC verification requires Python assertion checks')
P=Path(__file__).resolve().parents[1];R=P.parents[2];A=P/'adapter'

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def catalog():
 lock=tomllib.loads((R/'Cargo.lock').read_text())
 spec=next(item for item in lock['package'] if item['name']=='crc-catalog')
 checksum=spec['checksum'];prefix='crc-catalog-'+spec['version']
 assert spec['source'].startswith('registry+')
 path=R/'.work/cache'/(checksum+'.crate')
 if not path.exists():
  home=Path(os.environ.get('CARGO_HOME',str(Path.home()/'.cargo')))
  candidates=list((home/'registry/cache').glob('*/'+prefix+'.crate'))
  if candidates:shutil.copyfile(candidates[0],path)
  elif os.environ.get('CARGO_NET_OFFLINE')=='true':raise RuntimeError('Offline crc-catalog archive cache missing')
  else:
   url='https://crates.io/api/v1/crates/crc-catalog/'+spec['version']+'/download'
   with urllib.request.urlopen(url,timeout=60) as src,path.open('xb') as dst:shutil.copyfileobj(src,dst)
 if sha(path)!=checksum:raise RuntimeError('crc-catalog archive checksum mismatch')
 metadata=json.loads(subprocess.check_output(['cargo','metadata','--locked','--offline','--format-version','1','--manifest-path',R/'Cargo.toml'],text=True))
 package=next(p for p in metadata['packages'] if p['name']=='crc-catalog');root=Path(package['manifest_path']).parent
 assert (package['version'],package['source'])==(spec['version'],spec['source'])
 with tarfile.open(path) as tar:
  observed={}
  for member in tar:
   assert not Path(member.name).is_absolute() and '..' not in Path(member.name).parts
   assert member.name.rstrip('/')==prefix or member.name.startswith(prefix+'/')
   if member.isdir():continue
   assert member.isfile()
   rel=member.name[len(prefix)+1:];assert rel and rel not in observed
   data=tar.extractfile(member).read();observed[rel]={'sha256':hashlib.sha256(data).hexdigest(),'executable':bool(member.mode&0o111)}
 import sys
 sys.path.insert(0,str(R.parents[1]/'scripts'))
 from aeneas_management import source
 installed=source.inventory(root)
 for marker in ['.cargo-ok','.cargo-checksum.json']:installed.pop(marker,None)
 assert installed==observed,'Installed crc-catalog source inventory differs from its locked archive'

 return path

def main():
 parser=argparse.ArgumentParser();parser.add_argument('phase',choices=['native','extract','post']);a=parser.parse_args()
 run=Path(os.environ['AENEAS_RUN_DIR'])/('crc-'+P.name+'-'+a.phase);run.mkdir(parents=True,exist_ok=False)
 env=os.environ.copy();env['CRC_CATALOG_ARCHIVE']=str(catalog())
 def call(label,cmd,extract=False):
  selected=env.copy()
  if extract:selected['RUSTUP_TOOLCHAIN']=env['AENEAS_EXTRACT_RUST']
  with (run/(label+'.log')).open('w') as log:subprocess.run(list(map(str,cmd)),cwd=R,env=selected,stdout=log,stderr=subprocess.STDOUT,check=True)
  print('PASS',label,flush=True)
 if a.phase=='native':
  cases=[('debug',['--test','crc','--','--nocapture']),('release',['--release','--test','crc','--','--nocapture']),('upstream',['--lib','--test','upstream_crc']),('doc',['--doc'])]
  for label,args in cases:call('native-'+label,['cargo','test','--locked','--manifest-path',R/'Cargo.toml',*args])
  selected=env.copy();selected['CRC_NATIVE_LOG_DIR']=str(run)
  subprocess.run(['python3',R/'aeneas/profiles/default/adapter/native-results.py'],cwd=R,env=selected,check=True)
 elif a.phase=='extract':
  target={'Darwin':'aarch64-apple-darwin','Linux':'x86_64-unknown-linux-gnu'}[platform.system()]
  maintained=P/'proofs/Generated'/target
  groups=[]
  if P.name=='default':
   call('util',['python3',A/'extract-util.py','--output',run/'util'],True);groups.append((run/'util',maintained))
   for label,config in [('mono','mono.json')]+[(f'CloneFrom{n}',f'clone-from-{n}.json') for n in [0,1,16]]:
    call(label,['python3',A/'extract-mono.py','--config',P/'config'/config,'--output',run/label],True)
    groups.append((run/label,maintained if label=='mono' else maintained/label))
  else:
   for label,module in [('bridge','CrcStage2'),('public','CrcBody')]:
    call(label,['python3',A/f'extract-{label}.py','--output',run/label],True)
    groups.append((run/label,maintained/module))
   call('normalization-guards',['python3',A/'check-normalization-guards.py',run/'public/original.llbc',run/'public/crc_body.llbc','--output',run/'normalization-guards'])
  for generated,destination in groups:
   for source in generated.glob('*.lean'):
    if source.name=='FunsExternal_Template.lean':continue # exact sole standard-primitive templates checked by extractor; never imported
    assert source.read_bytes()==(destination/source.name).read_bytes(),source
 elif a.phase=='post':
  if P.name=='default':call('coverage',['python3',A/'check-coverage.py'])
  else:
   call('inventory',['python3',A/'inventory.py','--check']);call('coverage',['python3',A/'coverage.py','--check'])
   call('catalog-domains',['python3',A/'check-catalog-domains.py','--output',run/'catalog-domains.json'])
   assert (run/'catalog-domains.json').read_bytes()==(P/'config/catalog-domains.json').read_bytes()
   with (run/'aggregate.log').open('w') as log:subprocess.run(['lake','build','Stage2Proofs'],cwd=env['AENEAS_PROOF_DIR'],env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
 print('PASS local CRC checks; shared Lean audit remains independent:',run)
if __name__=='__main__':main()
