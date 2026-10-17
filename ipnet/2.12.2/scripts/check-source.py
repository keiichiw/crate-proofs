#!/usr/bin/env python3
"""Check captured release bytes and the unchanged implementation, offline."""
import hashlib
import json
import subprocess
import tomllib
from pathlib import Path
import tarfile
root = Path(__file__).resolve().parents[1]
capture = root / 'capture'
sha = lambda b: hashlib.sha256(b).hexdigest()
manifest = json.loads((capture / 'manifest.json').read_text())
assert sha((capture / 'registry-index.jsonl').read_bytes()) == manifest['registry_index_sha256']
index = [json.loads(s) for s in (capture / 'registry-index.jsonl').read_text().splitlines()]
release = next(r for r in index if r['vers'] == '2.12.2')
assert not release['yanked']
stable = [r for r in index if not r['yanked'] and all(x.isdigit() for x in r['vers'].split('.'))]
assert max(stable, key=lambda r: tuple(map(int, r['vers'].split('.'))))['vers'] == '2.12.2'
assert release['cksum'] == manifest['archive_sha256'] == sha((capture / 'release.crate').read_bytes())
with tarfile.open(capture / 'release.crate') as archive:
    files = {str(Path(m.name).relative_to('ipnet-2.12.2')): sha(archive.extractfile(m).read()) for m in archive if m.isfile()}
assert files == manifest['source_files_sha256']
assert files == {str(p.relative_to(capture / 'source')): sha(p.read_bytes()) for p in (capture / 'source').rglob('*') if p.is_file()}
pin = json.loads((root/'verification/upstream.json').read_text())
assert manifest['release_vcs_info']['git']['sha1'] == pin['commit']
assert json.loads((capture/'source/.cargo_vcs_info.json').read_text()) == manifest['release_vcs_info']
upstream = root/pin['path']
def git(directory, *args):
    return subprocess.check_output(['git', '-C', str(directory), *args])
assert (upstream/'.git').is_file(), 'Initialize the upstream submodule first'
assert git(upstream, 'rev-parse', 'HEAD').decode().strip() == pin['commit'], 'Wrong upstream commit'
assert not git(upstream, 'status', '--porcelain', '--untracked-files=all', '--ignored'), 'Dirty upstream tree'
repo = Path(git(root, 'rev-parse', '--show-toplevel').decode().strip())
relative = upstream.relative_to(repo).as_posix()
entry = git(repo, 'ls-files', '--stage', '--', relative).decode().strip()
assert entry == f"160000 {pin['commit']} 0\t{relative}", 'Gitlink differs from the approved pin'
assert git(repo, 'config', '-f', '.gitmodules', '--get', f"submodule.{pin['gitmodule_name']}.url").decode().strip() == pin['url']
assert git(repo, 'config', '-f', '.gitmodules', '--get', f"submodule.{pin['gitmodule_name']}.path").decode().strip() == relative
# Compare actual tracked bytes, even if someone sets assume-unchanged/skip-worktree.
for item in git(upstream, 'ls-tree', '-rz', 'HEAD').split(b'\0'):
    if not item: continue
    header, rawpath = item.split(b'\t', 1)
    mode, kind, oid = header.split()
    assert kind == b'blob' and mode in (b'100644', b'100755')
    path = upstream/rawpath.decode()
    assert not path.is_symlink()
    assert path.read_bytes() == git(upstream, 'cat-file', 'blob', oid.decode()), f'Changed upstream file: {path}'
outer = tomllib.loads((root/'Cargo.toml').read_text())
original = tomllib.loads((upstream/'Cargo.toml').read_text())
assert outer['lib']['path'] == 'upstream/src/lib.rs'
for key in ['features', 'dependencies', 'dev-dependencies']:
    assert outer.get(key, {}) == original.get(key, {}), f'Divergent Cargo {key}'
for key in ['name', 'version', 'edition']:
    assert outer['package'][key] == original['package'][key]
source = {str(p.relative_to(upstream)): sha(p.read_bytes()) for p in (upstream/'src').rglob('*') if p.is_file()}
assert source == {p: h for p, h in files.items() if p.startswith('src/')}
print('Pinned clean submodule, gitlink, Cargo build surface, and release src/ identity: OK')
