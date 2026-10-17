#!/usr/bin/env python3
import json, subprocess
from pathlib import Path
root = Path(__file__).resolve().parents[1]
pins = json.loads((root/'verification/toolchain.json').read_text())
def output(*cmd):
    return subprocess.check_output(cmd, cwd=root, text=True).strip()
for directory, key in [('.tools/aeneas','aeneas'), ('.tools/aeneas/charon','charon')]:
    assert output('git','-C',directory,'rev-parse','HEAD') == pins[key]
    expected_patch = (root/pins[key + '_local_patch']).read_text().strip()
    assert output('git','-C',directory,'diff','HEAD','--') == expected_patch, f'Unrecorded tool source modification: {directory}'
assert (root/'proofs/lean-toolchain').read_text().strip() == pins['lean']
packages = json.loads((root/'proofs/lake-manifest.json').read_text())['packages']
aeneas = next(p for p in packages if p['name']=='aeneas')
assert aeneas['rev'] == pins['aeneas']
assert aeneas['url'].rstrip('/') == 'https://github.com/AeneasVerif/aeneas'
assert aeneas['subDir'] == 'backends/lean'
for package in packages:
    directory = root / 'proofs/.lake/packages' / package['name']
    assert output('git', '-C', str(directory), 'rev-parse', 'HEAD') == package['rev'], package['name']
    expected_patch = (root/pins['aeneas_local_patch']).read_text().strip() if package['name'] == 'aeneas' else ''
    assert output('git', '-C', str(directory), 'diff', 'HEAD', '--') == expected_patch, f'Unrecorded Lean dependency modification: {package["name"]}'
    assert not output('git', '-C', str(directory), 'ls-files', '--others', '--exclude-standard'), f'Untracked Lean dependency source: {package["name"]}'
assert pins['cargo_proofs'] in output(str(root/'.tools/cargo-proofs/bin/cargo-proofs'),'--version')
print('Pinned tool sources, Lean dependency, and cargo-proofs version: OK')

assert output('git','-C','.tools/proofs-rs','rev-parse','HEAD') == pins['proofs_rs_revision']
patch = (root/'verification/patches/proofs-rs-audit-identifier.patch').read_text().strip()
assert output('git','-C','.tools/proofs-rs','diff','HEAD','--') == patch
print('Latest proofs-rs base plus exact audit-identifier compatibility patch: OK')

import hashlib
for name, expected in pins['tool_binaries_sha256'].items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest() == expected, f'Tool binary changed: {name}'
assert pins['native_rust'] in output('rustc', '--version')
assert output('rustup', 'run', pins['extraction_rust'], 'rustc', '--version', '--verbose') == pins['extraction_rustc_verbose']
target_cfg = output('rustup', 'run', pins['extraction_rust'], 'rustc', '--print', 'cfg').splitlines()
for key, value in pins['extraction_target_cfg'].items():
    assert f'{key}="{value}"' in target_cfg, f'Extraction target setting differs: {key}'
std_sources = json.loads((root/'verification/std-source-boundaries.json').read_text())
assert std_sources['rust_toolchain'] == pins['extraction_rust']
sysroot = Path(output('rustup', 'run', pins['extraction_rust'], 'rustc', '--print', 'sysroot'))
for name, expected in std_sources['files_sha256'].items():
    source = sysroot / 'lib/rustlib/src/rust/library' / name
    assert hashlib.sha256(source.read_bytes()).hexdigest() == expected, f'Reviewed standard-library source changed: {name}'
assert pins['lean'].split(':v')[1] in subprocess.check_output(['lake','env','lean','--version'],cwd=root/'proofs',text=True)
assert (root/'.tools/aeneas/charon-pin').read_text().strip().splitlines()[-1] == pins['charon']
print('Tool binary hashes, native Rust, and Charon compatibility pin: OK')
