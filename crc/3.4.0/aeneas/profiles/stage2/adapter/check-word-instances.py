#!/usr/bin/env python3
"""Check exact binder/result specialization and direct use of preserved contracts."""
from pathlib import Path
import json,re
if not __debug__:raise RuntimeError('CRC specialization checks require Python assertions')
P=Path(__file__).resolve().parents[1]
original=P/'proofs/Stage2Proofs/WordProtocols.lean'
source=original.read_text()
expected=['import Stage2Proofs.WordProtocols\nopen Aeneas Aeneas.Std Result\nnamespace CrcPublicWordInstances\n']
for width in [8,16,32,64,128]:
 for method in ['digest','digest_with_initial','digest_finalize']:
  name=f'{method}{width}_spec'
  match=re.search(r'theorem '+name+r' \{L : Usize\}\n(?P<header>.*?)(?= := by)',source,re.S)
  assert match,name
  for lane,supported in [(0,'Or.inl rfl'),(1,'Or.inr (Or.inl rfl)'),(16,'Or.inr (Or.inr rfl)')]:
   header=match['header']
   header,count=re.subn(r'\s*\(_?hL : SupportedL L\)','',header)
   assert count==1,name
   header=re.sub(r'\bL\b',f'{lane}#usize',header)
   arguments='self initial' if method=='digest_with_initial' else 'self'
   expected.append(f'theorem {method}{width}_lane{lane}_spec\n'+header+' := by\n'+f'  exact CrcPublicWords.{name} {arguments} ({supported}) hw\n\n')
expected.append('end CrcPublicWordInstances\n')
actual=(P/'proofs/Stage2Proofs/WordProtocolInstances.lean').read_text()
actual=re.sub(r'/\-.*?\-/','',actual,flags=re.S)
normalize=lambda s:re.sub(r'\s+',' ',s).strip()
assert normalize(actual)==normalize(''.join(expected)),'A wrapper binder, result, selected lane or proof body changed'
new=json.loads((P/'theorems.json').read_text())
# Check current specialized wrappers against their actual generic theorem bodies.
wrapper_names=set(re.findall(r'theorem ([A-Za-z0-9_]+)',actual))
checked_names={item['name'] for item in new['checked']}
assert all('CrcPublicWordInstances.'+name in checked_names for name in wrapper_names)
assert len(wrapper_names)==len(expected[:-1])-1
assert len(new['recorder_mappings'])==75
assert len({x['theorem'] for x in new['recorder_mappings']})==75
print('PASS current generic theorem specialization, wrapper binders/results/proof bodies and API mappings')
