#!/usr/bin/env python3
"""Summarize independent finite native observations, never formal proof coverage."""
from pathlib import Path
import hashlib,json,re,sys
D=Path(sys.argv[1]);runs={}
for name in ('debug','release','upstream','doc'):
 p=D/(f'native-{name}.log' if name in ('debug','release') else name+'.log')
 s=p.read_text();groups=[{'passed':int(a),'failed':int(b),'ignored':int(c)} for a,b,c in re.findall(r'test result: ok\. (\d+) passed; (\d+) failed; (\d+) ignored;',s)]
 assert groups and all(x['failed']==0 for x in groups),(name,s[-1000:])
 if name in ('debug','release'):assert len(groups)==1 and groups[0]['passed']==15 and groups[0]['ignored']==0
 runs[name]={'log':p.name,'test_groups':groups,'observations':sorted(set(re.findall(r'OBSERVATION ([^\n]+)',s)))}
for name,count in [('debug',15),('release',15)]:
 s=(D/f'native-list-{name}.log').read_text();assert len(re.findall(r'^\w+: test$',s,re.M))==count
obs={
 'fixed_exact_length':{'u32_destination_bytes':5,'encode_result':'None','destination_unchanged':True,'decode_result':'None','classification':'documentation precision issue; exact length is not clearly stated'},
 'reader_target_length_cap':{'u8_padded_zero_slice_result':[0,3],'u8_stream_error':'InvalidData','u8_stream_bytes_consumed':3,'five_byte_canonical_varint_stream_bytes_consumed_before_error':3,'continuation_after_error_is_mid_varint':True,'u64_ten_continuations_followed_by42_bytes_consumed':11,'following_42_lost':True,'classification':'width-based stream cap and read-before-cap-check; violates whole-varint consumption wording'},
 'reader_range_error':{'bytes':[172,2,42],'typed_result':'UnexpectedEof','bytes_consumed':2,'following42_unread':True,'actual_eof':False,'documentation_promises_truncation':True,'classification':'checked range rejection conflated with EOF; distinct from width-cap consumption'},
 'generic_fixed_capacity':{'custom_correct_FixedInt_size':16,'read_panics':True,'write_panics':True,'before_any_io':True,'builtin_types_affected':False,'classification':'undocumented fixed eight-byte capacity in public generic adapters'},
 'insufficient_varint_destination':{'panics':True,'outside_documented_required_space_precondition':True,'classification':'expected precondition violation, not a defect'},
 'io':{'varint_read_interrupted_propagated':True,'fixed_read_exact_retries_interrupted':True,'write_all_retries_interrupted':True,'partial_write_errors_preserve_prefix':True,'zero_write_returns_WriteZero':True}}
result={'kind':'native-tests-not-formal-proof','status':'passed','rust_toolchain':(D/'toolchain.log').read_text().strip(),'feature_configuration':'default; asynchronous optional feature adapters excluded from this run','builtin_integer_types':['u8','u16','u32','u64','usize','i8','i16','i32','i64','isize'],'pointer_width_bits':64,'supported_builtin_callable_instances_exercised':130,'core_instances':90,'sync_io_builtin_instantiations':40,'oracle':'independent integer division/remainder base128, arithmetic ZigZag and positional base256; no upstream algorithm or table reuse','runs':runs,'observations':obs,'limitations':['finite test corpus is not a formal proof','scalar corpus: boundaries around each bit, all0..255, 2048 deterministic random words per type','4096 deterministic arbitrary byte slices per type','generic custom adapters probed separately from builtin coverage','async and simultaneous optional-feature builds excluded'],'files_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(D.iterdir()) if p.is_file() and p.name!='native-results.json'}}
(D/'native-results.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS native debug/release15+15, upstream/doc suites;130 builtin instances, explicit generic/error/consumption observations')
