#!/usr/bin/env python3
import json, subprocess
from pathlib import Path
root = Path(__file__).resolve().parents[1]
pins = json.loads((root/'verification/toolchain.json').read_text())
def output(*cmd):
    return subprocess.check_output(cmd, cwd=root, text=True).strip()
for directory, key in [('.tools/aeneas','aeneas'), ('.tools/aeneas/charon','charon')]:
    assert output('git','-C',directory,'rev-parse','HEAD') == pins[key]
    assert not output('git','-C',directory,'diff','HEAD','--'), f'Modified tool source: {directory}'
assert (root/'proofs/lean-toolchain').read_text().strip() == pins['lean']
packages = json.loads((root/'proofs/lake-manifest.json').read_text())['packages']
aeneas = next(p for p in packages if p['name']=='aeneas')
assert aeneas['rev'] == pins['aeneas']
assert aeneas['url'].rstrip('/') == 'https://github.com/AeneasVerif/aeneas'
assert aeneas['subDir'] == 'backends/lean'
for package in packages:
    directory = root / 'proofs/.lake/packages' / package['name']
    assert output('git', '-C', str(directory), 'rev-parse', 'HEAD') == package['rev'], package['name']
    assert not output('git', '-C', str(directory), 'diff', 'HEAD', '--'), f'Modified Lean dependency: {package["name"]}'
    assert not output('git', '-C', str(directory), 'ls-files', '--others', '--exclude-standard'), f'Untracked Lean dependency source: {package["name"]}'
assert pins['cargo_proofs'] in output(str(root/'.tools/cargo-proofs/bin/cargo-proofs'),'--version')
print('Pinned tool sources, Lean dependency, and cargo-proofs version: OK')

assert output('git','-C','.tools/proofs-rs','rev-parse','HEAD') == pins['proofs_rs_revision']
patch = (root/'verification/patches/proofs-rs-audit-identifier.patch').read_text().strip()
assert output('git','-C','.tools/proofs-rs','diff','HEAD','--') == patch
print('Latest proofs-rs base plus exact audit-identifier compatibility patch: OK')
