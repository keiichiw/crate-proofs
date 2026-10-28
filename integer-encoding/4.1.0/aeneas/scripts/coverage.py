#!/usr/bin/env python3
"""Count closed builtin scalar contracts, without counting generic I/O as finite APIs."""
from pathlib import Path
import argparse,json
R=Path(__file__).resolve().parents[1];p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
ms=json.loads((R/'aeneas/profiles/default/api-mappings.json').read_text());byapi={m['api']:m for m in ms};assert len(byapi)==len(ms)==80
rows=[]
for ty in ('u8','u16','u32','u64','usize','i8','i16','i32','i64','isize'):
 for trait,methods in [('VarInt',('required_space','encode_var','decode_var','encode_var_vec')),('FixedInt',('encode_fixed','encode_fixed_light','decode_fixed','encode_fixed_vec','switch_endianness'))]:
  for method in methods:
   api=f'<{ty} as integer_encoding::{trait}>::{method}';row={'api':api,'type':ty,'family':trait,'method':method,'formal':api in byapi}
   if api in byapi:
    row.update(byapi[api]);assert ('Platform.numBits = 64' in row['precondition'])==(ty in ('usize','isize') and trait=='FixedInt'),row
   else:assert trait=='VarInt' and method=='decode_var';row['blocker']='frozen Aeneas iterator mutable-borrow loop join; additional raw-pointer/control-flow limitations; no partial model accepted'
   rows.append(row)
assert len(rows)==90 and len({x['api'] for x in rows})==90
obj={'denominator':'90 supported builtin scalar callable instances: ten types times four VarInt and five FixedInt methods; associated items and generic/async I/O excluded', 'builtin_scalar_callable_instances':90,'formal_builtin_scalar_instances':80,'formal_builtin_scalar_percent':100*80/90,'formal_varint_instances':30,'varint_instances':40,'formal_fixed_instances':50,'fixed_instances':50,'error_contracts_not_extra_instances':10,'extraction_profile':'unchanged source, default features, debug assertions enabled; successful encoding assumes documented capacity, short-buffer failure root specifically debug profile','pointer_domain':'fixed-width usize/isize contracts require System.Platform.numBits = 64, matching the native 64-bit target','standard_model_boundary':'selected scalar size_of; standard U8 slice cloning; six pointer endian aliases; selected unwrap Debug erasure; existing idealized Std allocation; see trust-boundary.md','vec_structural_boundary':'source default selection plus actual used dictionary fields reviewed; unused fields universally quantified, no assumed correctness law','formal_sync_io_families':0,'sync_io_native_builtin_instantiations':40,'formal_async_io_families':0,'native_builtin_matrix_instances':130,'native_default_features_only':True,'whole_crate_api_percentage_claimed':False,'rows':rows}
p=R/'aeneas/profiles/default/coverage.json';s=json.dumps(obj,indent=2)+'\n'
if a.check:assert p.read_text()==s
else:p.write_text(s)
print('PASS80/90 closed builtin scalar contracts; formal I/O excluded; native130 separate')
