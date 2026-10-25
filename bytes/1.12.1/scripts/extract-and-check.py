#!/usr/bin/env python3
"""Regenerate every maintained model; never rewrite maintained Lean."""
import json,os,subprocess,sys
from pathlib import Path
r=Path(__file__).resolve().parents[1];p=r/'aeneas/profiles/default'
run=Path(os.environ['AENEAS_RUN_DIR']);pins=json.loads((p/'toolchain.lock.json').read_text())
env=dict(os.environ,RUSTUP_TOOLCHAIN=pins['extraction_rust'])
# Compiler-level source provenance remapping makes harness spans independent of checkout path.
env['CARGO_ENCODED_RUSTFLAGS']='--remap-path-prefix='+str(r)+'=/crate/bytes/1.12.1'
jobs=[('base','Bytes',None),('consumption','BytesConsumption',None),('adapters','BytesAdapters',None),('copy','BytesCopy',None),('cursor','BytesCursorSlice',None),('reader','BytesReader',None),('numeric','BytesNumeric','numeric'),('range','BytesRange','stage3'),('extended-copy','BytesExtendedCopy','stage3')]
for label,model,tool in jobs:
 out=run/(label+'-generated')
 if label=='base':argv=[sys.executable,str(r.parents[1]/'scripts/aeneas-extract.py'),str(r),'--config',str(p/'extraction.json'),'--output',str(out)]
 else:argv=[sys.executable,str(r/'scripts'/('extract-'+label+'.py')),'--output',str(out)]
 if tool:argv+=['--aeneas',env['AENEAS_'+tool.upper()+'_BIN']]
 subprocess.run(argv,cwd=r,env=env,check=True)
 target=__import__('platform').machine()
 target='aarch64-apple-darwin' if sys.platform=='darwin' else 'x86_64-unknown-linux-gnu'
 if (out/(model+'.lean')).read_bytes()!=(p/'proofs/Generated'/target/(model+'.lean')).read_bytes():raise ValueError('Fresh generated model differs: '+model)
print('All nine actual models match maintained target bytes')
