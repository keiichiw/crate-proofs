#!/usr/bin/env python3
"""Explicit, additive migration of simple Aeneas profiles (never updates proofs)."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import tomllib

from aeneas_management import source

REPO = Path(__file__).resolve().parents[1]
BASE = REPO / 'adler2/2.0.1/.work/selected-tools/aeneas'
AENEAS = 'be86ab0f1989d04944292b345b24c435be3ad10a'
CHARON = '08d7c9d50144bd84848212c24701253585e90d1f'


def lock_source(root):
    archive = root / 'capture/release.crate'
    if not archive.exists():
        archive = root / f'capture/{root.parent.name}-{root.name}.crate'
    metadata = root / 'capture/manifest.json'
    checksum = source.digest(archive)
    if metadata.exists():
        saved = json.loads(metadata.read_text())
        if saved.get('archive_sha256', checksum) != checksum:
            raise ValueError('Captured registry checksum mismatch')
    with tempfile.TemporaryDirectory() as temp:
        expanded = Path(temp)
        source.extract_archive(archive, expanded, f'{root.parent.name}-{root.name}')
        lock = {'schema_version': 1, 'kind': 'registry', 'name': root.parent.name, 'version': root.name,
                'url': f'https://static.crates.io/crates/{root.parent.name}/{root.parent.name}-{root.name}.crate',
                'sha256': checksum, 'files': source.inventory(expanded), 'aliases': ['upstream', 'capture/source']}
        if (root / 'Cargo.toml').exists():
            outer = tomllib.loads((root / 'Cargo.toml').read_text())
            original = tomllib.loads((expanded / 'Cargo.toml').read_text())
            exceptions = {}
            for key in ('features', 'dependencies', 'build-dependencies', 'target'):
                if outer.get(key, {}) != original.get(key, {}):
                    exceptions[key] = 'Historical verification manifest differs; see original Cargo.toml and scope documentation. Not a full release-build equivalence claim.'
            for key in ('name', 'version', 'edition', 'links', 'build'):
                default = '2015' if key == 'edition' else None
                if outer['package'].get(key, default) != original['package'].get(key, default):
                    exceptions['package.' + key] = 'Retained historical verification manifest setting; review before extending coverage.'
            lock['manifest_exceptions'] = exceptions
        source.write_json(root / 'source.lock.json', lock)
    cache = root / '.work/cache'
    cache.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(archive, cache / (checksum + '.crate'))
    source.restore(root, offline=True)
    return lock


def combined_patch(root, patches, added=None):
    with tempfile.TemporaryDirectory() as temp:
        tmp = Path(temp)
        (tmp / 'objects').mkdir()
        env = dict(os.environ, GIT_INDEX_FILE=str(tmp / 'index'), GIT_OBJECT_DIRECTORY=str(tmp / 'objects'),
                   GIT_ALTERNATE_OBJECT_DIRECTORIES=str(BASE / '.git/objects'))
        def git(*args, input=None):
            return subprocess.check_output(['git', '-C', str(BASE), *args], env=env, input=input)
        git('read-tree', AENEAS)
        for patch in patches:
            git('apply', '--cached', '--binary', str(patch))
        for name, path in (added or {}).items():
            oid = git('hash-object', '-w', '--stdin', input=path.read_bytes()).decode().strip()
            git('update-index', '--add', '--cacheinfo', '100644', oid, name)
        return git('diff', '--cached', '--binary', AENEAS), git('write-tree').decode().strip()


def tool_lock(root, profile, patches=(), added=None):
    data, tree = combined_patch(root, patches, added)
    directory = profile / 'patches'
    directory.mkdir(exist_ok=True)
    patch_list = []
    if data:
        patch = directory / 'aeneas.patch'
        patch.write_bytes(data)
        patch_list.append({'file': 'patches/aeneas.patch', 'sha256': source.digest(patch),
                           'purpose': 'Preserved existing extractor/backend compatibility changes; see legacy toolchain documentation',
                           'regressions': 'Regenerate maintained models and run theorem/axiom audits'})
    opam = REPO / 'adler2/2.0.1/aeneas/profiles/default/opam.locked'
    shutil.copyfile(opam, profile / 'opam.locked')
    cli = REPO / 'adler2/2.0.1/.work/selected-tools/proofs-rs'
    cli_rev = subprocess.check_output(['git', '-C', str(cli), 'rev-parse', 'HEAD']).decode().strip()
    lock = {'schema_version': 1, 'recipe': 'aeneas-opam-v1', 'native_rust': '1.91.1',
            'extraction_rust': 'nightly-2026-09-17', 'lean': 'leanprover/lean4:v4.35.0',
            'opam_sha256': source.digest(profile / 'opam.locked'),
            'repositories': {
                'aeneas': {'url': 'https://github.com/AeneasVerif/aeneas.git', 'revision': AENEAS, 'tree': tree, 'patches': patch_list},
                'charon': {'url': 'https://github.com/AeneasVerif/charon.git', 'revision': CHARON,
                           'tree': subprocess.check_output(['git', '-C', str(BASE / 'charon'), 'rev-parse', CHARON + '^{tree}']).decode().strip(), 'patches': []},
                'proofs-rs': {'url': 'https://github.com/proofs-rs/proofs-rs.git', 'revision': cli_rev,
                             'tree': subprocess.check_output(['git', '-C', str(cli), 'rev-parse', cli_rev + '^{tree}']).decode().strip(), 'patches': []}}}
    source.write_json(profile / 'toolchain.lock.json', lock)


def migrate_simple(root):
    if (root / 'aeneas/profiles/default').exists():
        raise ValueError('Profile already exists; migration never overwrites maintained inputs')
    profile = root / 'aeneas/profiles/default'
    profile.mkdir(parents=True)
    shutil.copytree(root / 'proofs', profile / 'proofs', ignore=shutil.ignore_patterns('.lake', '*.olean', '*.ilean'))
    shutil.copyfile(root / 'proofs.toml', profile / 'proofs.toml')
    shutil.copyfile(root / 'verification/theorems.json', profile / 'theorems.json')
    spec = root / 'verification/specification.md'
    if not spec.exists():
        spec = root / 'README.md'
    shutil.copyfile(spec, profile / 'specification.md')
    shutil.copyfile(root / 'verification/results.md', profile / 'historical-results.md')
    (profile / 'results.md').write_text('# Managed profile\n\nNo fresh managed-profile proof run has been accepted. See historical-results.md for the previous layout only.\n')
    extraction = root / 'verification/aeneas.json'
    if extraction.exists():
        config = json.loads(extraction.read_text())
    else:
        config = {'entries': ['crate::Adler32::new', 'crate::Adler32::from_checksum', 'crate::Adler32::checksum',
                             'crate::Adler32::write_slice', 'crate::adler32_slice'],
                  'llbc': 'adler2.llbc', 'cargo_args': ['--lib', '--locked'],
                  'models': {'Adler2.lean': ['Adler32.new', 'Adler32.from_checksum', 'Adler32.checksum',
                      'algo.U32X4.from', 'algo.Adler32.compute', 'Adler32.write_slice', 'adler32_slice']}}
    source.write_json(profile / 'extraction.json', config)
    verification = {'schema_version': 1, 'cargo_root': '.', 'supported_targets': ['aarch64-apple-darwin', 'x86_64-unknown-linux-gnu'],
                    'native': [['cargo', 'test', '--locked'], ['cargo', 'test', '--locked', '--no-default-features']],
                    'extractions': [{'config': 'extraction.json', 'cwd': '.',
                                      'models': {name: 'proofs/' + name for name in config['models']}}],
                    'lean_dir': 'proofs', 'inventory': 'theorems.json', 'report': 'proofs.toml'}
    source.write_json(profile / 'verification.json', verification)
    (root / 'aeneas/profiles.toml').write_text('default = "default"\n\n[profiles.default]\npath = "aeneas/profiles/default"\ndependencies = []\n')
    patches = []
    if root.parent.name == 'shell-words':
        old = json.loads((root / 'verification/toolchain.json').read_text())
        patches = [root / 'verification/patches' / p['file'] for p in old['patches']]
    tool_lock(root, profile, patches)
    lake = profile / 'proofs/lakefile.toml'
    text = lake.read_text()
    import re
    text = re.sub(r'git = \{[^\n]+\}\nrev = "[^"]+"', 'path = "@AENEAS_BACKEND@"', text)
    lake.write_text(text)
    lock_source(root)
    origin = {p.relative_to(root).as_posix(): source.digest(p) for p in (root / 'proofs').rglob('*') if p.is_file() and '.lake' not in p.parts}
    source.write_json(profile / 'migration-origin.json', {'inputs': origin, 'historical_evidence_is_not_fresh': True})
    print(f'Prepared additive managed profile: {root}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('crate', type=Path)
    parser.add_argument('--source-only', action='store_true')
    args = parser.parse_args()
    root = args.crate.resolve()
    if not root.is_relative_to(REPO) or len(root.relative_to(REPO).parts) != 2:
        raise ValueError('Expected repository crate/version directory')
    lock_source(root) if args.source_only else migrate_simple(root)
