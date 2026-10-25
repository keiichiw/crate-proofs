#!/usr/bin/env python3
"""Preserve the release, harness and reviewed compiler/model boundaries."""
import hashlib,json,os,subprocess,sys,tomllib
from pathlib import Path
r=Path(__file__).resolve().parents[1];p=r/'aeneas/profiles/default'
sys.path.insert(0,str(r.parents[1]/'scripts'))
from aeneas_management import source,tools
if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE','') not in ('','0'):
 raise ValueError('Assertions must be enabled')
lock=json.loads((r/'source.lock.json').read_text());source.check(r/'.work/source',lock)
if lock['sha256']!='fc652a48c352aef3ea3aed32080501cf3ef6ed5da78602a020c991775b0aff04':raise ValueError('Release checksum differs')
if json.loads((r/'.work/source/.cargo_vcs_info.json').read_text())['git']['sha1']!='76c0fbb54ed4336caf9d2311658a2f4a5627c21d':raise ValueError('Release VCS identity differs')
# Complete normalized release manifest equality, with only source paths/workspace relocated.
expected=tomllib.loads((r/'.work/source/Cargo.toml').read_text().replace('path = "','path = ".work/source/'))
expected['workspace']={'exclude':['.work','tests','aeneas']}
if tomllib.loads((r/'Cargo.toml').read_text())!=expected:raise ValueError('Outer release manifest/workspace differs')
stores={}
for role,d in [('core',p),('numeric',p/'numeric'),('stage3',p/'stage3'),('ordinary',p/'ordinary')]:
 tool_lock,key=tools.identity(d);store=r.parents[1]/'.work/tools'/key;tools.check(store,tool_lock);stores[role]=store/'aeneas'
 if role=='ordinary':continue
 repair=json.loads((p/('tool-repair.json' if role=='core' else role+'-tool-repair.json')).read_text())
 if tool_lock['repositories']['aeneas']['revision']!=repair['base_revision']:raise ValueError('Repair base mismatch')
 actual=set(subprocess.check_output(['git','-C',str(store/'aeneas'),'diff','--cached','--name-only',repair['base_revision'],'--'],text=True,env=dict(os.environ,GIT_OPTIONAL_LOCKS='0')).splitlines())
 if actual!=set(repair['changed_files']) or set(repair['changed_files'])!=set(repair['source_files_sha256']):raise ValueError('Repair inventory incomplete')
 for name,sha in repair['source_files_sha256'].items():
  if source.digest(store/'aeneas'/name)!=sha:raise ValueError('Reviewed repair source differs: '+name)
 if source.digest(r/repair['patch'])!=repair['patch_sha256']:raise ValueError('Original reviewed patch differs')
core_manifest=json.loads((p/'tool-repair.json').read_text());numeric_manifest=json.loads((p/'numeric-tool-repair.json').read_text());stage3_manifest=json.loads((p/'stage3-tool-repair.json').read_text())
changed=set(core_manifest['changed_files'])|set(numeric_manifest['changed_files'])
if {n for n in changed if (stores['core']/n).read_bytes()!=(stores['numeric']/n).read_bytes()}!=set(numeric_manifest['additional_changed_files_from_core']) or set(numeric_manifest['additional_changed_files_from_core'])!={'src/Config.ml','src/Main.ml','src/PrePasses.ml'}:raise ValueError('Numeric repair delta changed')
changed=set(numeric_manifest['changed_files'])|set(stage3_manifest['changed_files'])
expected={'backends/lean/Aeneas/Std.lean','backends/lean/Aeneas/Std/BytesStage3Types.lean','backends/lean/Aeneas/Std/BytesStage3Formatting.lean','backends/lean/Aeneas/Std/BytesStage3Registration.lean','backends/lean/Aeneas/Std/Core/Fmt.lean','src/Config.ml','src/Main.ml','src/Translate.ml','src/extract/ExtractBuiltinLean.ml','src/interp/InterpStatements.ml'}
if {n for n in changed if not (stores['numeric']/n).exists() or (stores['numeric']/n).read_bytes()!=(stores['stage3']/n).read_bytes()}!=expected:raise ValueError('Stage3 repair delta changed')
# Each auxiliary extractor and the proof backend share the unchanged core projection.
for name in ['backends/lean/Aeneas/Std/BytesBuf.lean']:
 if len({(s/name).read_bytes() for role,s in stores.items() if role!='ordinary'})!=1:raise ValueError('Core backend correspondence differs')
preludes={'backends/lean/Aeneas/Std/BytesStage3Types.lean':'proofs/BytesStage3Types.lean','backends/lean/Aeneas/Std/BytesStage3Formatting.lean':'proofs/BytesStage3Formatting.lean'}
if stage3_manifest['prelude_copies']!=preludes:raise ValueError('Incomplete stage3 compiler/application correspondence')
for backend,application in preludes.items():
 if (stores['stage3']/backend).read_bytes()!=(p/application).read_bytes():raise ValueError('Stage3 model correspondence differs')
for name,package,std in [('consumption','bytes_consumption',False),('adapters','bytes_adapters',False),('numeric','bytes_numeric',False),('cursor','bytes_cursor_slice',True)]:
 d=r/'tests'/name;actual=tomllib.loads((d/'Cargo.toml').read_text());dep={'path':'../../.work/source','default-features':std}
 if std:dep['features']=['std']
 expected={'package':{'name':package,'version':'0.1.0','edition':'2021'},'dependencies':{'bytes':dep},'workspace':{}}
 if actual!=expected:raise ValueError('Harness manifest changed: '+name)
 if not (d/'src/lib.rs').is_file() or d.is_symlink() or any(q.is_symlink() for q in (d/'src').rglob('*')):raise ValueError('Harness must contain regular source files')
std=p/'stdlib-source';manifest=json.loads((std/'manifest.json').read_text());pins=json.loads((p/'toolchain.lock.json').read_text())
if manifest['rust_toolchain']!=pins['extraction_rust']:raise ValueError('Rust source pin differs')
if set(manifest['files_sha256'])!={'library/core/src/convert/num.rs','library/core/src/convert/mod.rs','library/core/src/io/cursor.rs','library/core/src/ops/range.rs'}:raise ValueError('Standard source inventory differs')
sysroot=Path(subprocess.check_output(['rustup','run',pins['extraction_rust'],'rustc','--print','sysroot'],text=True).strip())
for name,sha in manifest['files_sha256'].items():
 if not (std/name).is_file() or (std/name).is_symlink():raise ValueError('Captured standard source must be regular: '+name)
 if source.digest(std/name)!=sha or source.digest(sysroot/'lib/rustlib/src/rust'/name)!=sha:raise ValueError('Standard source differs: '+name)
print('Immutable release, exact harness surfaces, all four tool receipts, reviewed repair sources and standard source correspondence: OK')
