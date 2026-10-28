#!/usr/bin/env python3
"""Fail closed on primitive source identity and actual supported call domains."""
from pathlib import Path
import json,hashlib,re,collections,os,subprocess
R=Path(__file__).resolve().parents[1];m=json.loads((R/'aeneas/profiles/default/stdlib.json').read_text());b=Path(subprocess.check_output(['rustup','run',m['toolchain'],'rustc','--print','sysroot'],text=True).strip())/'lib/rustlib/src/rust/library/core/src'
for n,x in m['files'].items():assert hashlib.sha256((b/n).read_bytes()).hexdigest()==x['sha256'],n
expected=[]
for n,x in m['files'].items():
 src=(b/n).read_text().splitlines()
 for lo,hi in x['excerpt_ranges']:
  expected.append(f'{n}:{lo}-{hi}');expected.extend(f'{i}: {src[i-1]}' for i in range(lo,hi+1));expected.append('')
assert (R/'aeneas/profiles/default/stdlib-excerpts.txt').read_text()=='\n'.join(expected)+'\n'
s=(R/('aeneas/profiles/default/proofs/Generated/'+subprocess.check_output(['rustc','-vV'],text=True).split('host: ')[1].splitlines()[0]+'/IntegerFixedDirect/Funs.lean')).read_text();types=('U8','U16','U32','U64','Usize','I8','I16','I32','I64','Isize')
calls=re.findall(r'core.mem.size_of Std.(\w+)',s);assert collections.Counter(calls)==collections.Counter({t:2 for t in types})
assert s.count('core.mem.size_of')==20 and s.count('core.slice.Slice.clone_from_slice')==10
assert s.count('core.slice.Slice.clone_from_slice core.clone.CloneU8 dst s')==10
r=(R/'aeneas/profiles/default/proofs/IntegerFixedDirect/FunsExternal.lean').read_text();names=re.findall(r'^(?:noncomputable )?def ([\w.]+)',r,re.M)
assert names==['core.mem.size_of','core.slice.Slice.clone_from_slice']+[f'core.num.{t}.{f}' for t in ('Usize','Isize') for f in ('to_le_bytes','to_be_bytes','from_le_bytes')]+['core.fmt.DebugTryFromSliceError','core.result.Result.unwrap']
assert not re.search(r'(?m)^\s*(?:axiom|opaque|partial\s+def)\b|\b(?:sorry|admit|native_decide)\b',r)
assert s.count('core.result.Result.unwrap core.fmt.DebugTryFromSliceError r')==10
assert s.count('core.result.Result.unwrap')==10 and s.count('core.fmt.DebugTryFromSliceError')==10
print('PASS original stdlib hashes/excerpts;20 scalar size_of,10 standard U8 clone calls; six explicit pointer aliases and selected unwrap Debug erasure; no application model substitutions')
