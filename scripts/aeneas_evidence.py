#!/usr/bin/env python3
"""Archive local evidence without publishing it or manufacturing proof results.

Archives are content addressed, independently verified, and never prerequisites of
setup/verify. Committed summaries describe the original inputs, not the checkout
in which this packaging command happens to run.
"""
import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import tarfile
import tempfile


def encode(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_sha(path):
    with Path(path).open('rb') as handle:
        return hashlib.file_digest(handle, 'sha256').hexdigest()


def safe_name(name):
    path = PurePosixPath(name)
    if not name or path.is_absolute() or '..' in path.parts or str(path) != name or '\\' in name:
        raise ValueError('Unsafe archive path: ' + name)
    return name


def inventory(root):
    root = Path(root)
    if root.is_symlink() or not root.is_dir():
        raise ValueError('Evidence must be a real directory')
    result = {}
    for path in sorted(root.rglob('*')):
        if path.is_symlink():
            raise ValueError('Evidence symlink: ' + str(path))
        if path.is_dir():
            continue
        if not path.is_file():
            raise ValueError('Evidence is not a regular file: ' + str(path))
        name = safe_name(path.relative_to(root).as_posix())
        result[name] = {'sha256': file_sha(path), 'bytes': path.stat().st_size,
                        'mode': path.stat().st_mode & 0o777}
    return result


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    # Never replace an existing evidence record silently.
    with path.open('xb') as handle:
        handle.write(encode(value))


def archive(root, store):
    root, store = Path(root).resolve(), Path(store).resolve()
    if store == root or store.is_relative_to(root):
        raise ValueError('Archive store must be outside the evidence tree')
    files = inventory(root)
    manifest = encode({'schema_version': 1, 'files': files})
    store.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.packing-', dir=store) as temporary:
        pending = Path(temporary) / 'archive.tar.gz'
        with pending.open('wb') as raw, gzip.GzipFile(fileobj=raw, mode='wb', mtime=0, filename='') as gz:
            with tarfile.open(fileobj=gz, mode='w') as tar:
                def add(name, data, mode):
                    item = tarfile.TarInfo(name)
                    item.size, item.mode, item.mtime = len(data), mode, 0
                    tar.addfile(item, io.BytesIO(data))
                add('manifest.json', manifest, 0o644)
                for name, expected in files.items():
                    data = (root / name).read_bytes()
                    if sha(data) != expected['sha256'] or len(data) != expected['bytes']:
                        raise ValueError('Evidence changed during packing: ' + name)
                    add('payload/' + name, data, expected['mode'])
        if inventory(root) != files:
            raise ValueError('Evidence tree changed during packing')
        checksum = file_sha(pending)
        destination = store / (checksum + '.tar.gz')
        if destination.exists():
            if file_sha(destination) != checksum:
                raise ValueError('Corrupt existing archive')
        else:
            os.replace(pending, destination)
    record = {'schema_version': 1, 'kind': 'local-evidence-archive',
              'availability': 'local-only', 'public_url': None,
              'archive': destination.name, 'sha256': checksum,
              'manifest_sha256': sha(manifest), 'files': len(files),
              'uncompressed_bytes': sum(x['bytes'] for x in files.values()),
              'compressed_bytes': destination.stat().st_size,
              'member_root': 'payload/',
              'scope': 'Original execution records; not a new verification or SARIF result.'}
    verify(record, store)
    return record


def verify(record, store):
    name = safe_name(record['archive'])
    if '/' in name or name != record['sha256'] + '.tar.gz':
        raise ValueError('Invalid content address')
    path = Path(store) / name
    if path.is_symlink() or file_sha(path) != record['sha256']:
        raise ValueError('Archive checksum mismatch')
    with tarfile.open(path, 'r:gz') as tar:
        members = tar.getmembers()
        names = [safe_name(m.name) for m in members]
        if len(set(names)) != len(names) or any(not m.isfile() for m in members):
            raise ValueError('Duplicate or non-regular archive member')
        if 'manifest.json' not in names:
            raise ValueError('Missing archive manifest')
        raw = tar.extractfile('manifest.json').read()
        if sha(raw) != record['manifest_sha256']:
            raise ValueError('Manifest checksum mismatch')
        data = json.loads(raw)
        if data['schema_version'] != 1:
            raise ValueError('Unsupported archive manifest')
        files = data['files']
        expected_names = {'manifest.json'} | {'payload/' + safe_name(n) for n in files}
        if set(names) != expected_names or len(files) != record['files']:
            raise ValueError('Missing or extra archive member')
        if sum(x['bytes'] for x in files.values()) != record['uncompressed_bytes']:
            raise ValueError('Archive size inventory mismatch')
        for name, entry in files.items():
            member = tar.getmember('payload/' + name)
            with tar.extractfile(member) as handle:
                checksum = hashlib.file_digest(handle, 'sha256').hexdigest()
            if (checksum != entry['sha256'] or member.size != entry['bytes']
                    or member.mode != entry['mode'] or not 0 <= member.mode <= 0o777):
                raise ValueError('Archive member mismatch: ' + name)
    return files


def restore(record, store, destination):
    destination = Path(destination)
    if destination.exists() or destination.is_symlink():
        raise ValueError('Restore destination must not exist')
    files = verify(record, store)
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.restoring-', dir=destination.parent) as temporary:
        tree = Path(temporary) / 'tree'
        tree.mkdir()
        with tarfile.open(Path(store) / record['archive'], 'r:gz') as tar:
            for name, entry in files.items():
                path = tree / safe_name(name)
                path.parent.mkdir(parents=True, exist_ok=True)
                with tar.extractfile('payload/' + name) as src, path.open('xb') as out:
                    shutil.copyfileobj(src, out)
                path.chmod(entry['mode'])
        if inventory(tree) != files:
            raise ValueError('Restored bytes or modes differ')
        # A competing restore cannot overwrite a populated destination.
        if destination.exists() or destination.is_symlink():
            raise ValueError('Restore destination appeared during restore')
        tree.rename(destination)


def summarize(run, record, member_prefix=''):
    """Summarize a managed runner receipt; never trust a script exit code alone."""
    run = Path(run)
    result = json.loads((run / 'result.json').read_text())
    audit = json.loads((run / 'audit/result.json').read_text())
    before, after = (run / 'inputs-before.json'), (run / 'inputs-after.json')
    if result['status'] != 'passed' or audit['status'] != 'passed':
        raise ValueError('Cannot summarize a failed run as accepted')
    if json.loads(before.read_text()) != json.loads(after.read_text()):
        raise ValueError('Before/after fingerprints differ')
    for base, receipt in [(run, result), (run / 'audit', audit)]:
        for name, checksum in receipt['files_sha256'].items():
            path = base / safe_name(name)
            if path.is_symlink() or not path.is_file() or file_sha(path) != checksum:
                raise ValueError('Missing or changed run artifact: ' + name)
    prefix = member_prefix.rstrip('/')
    def ref(path):
        relative = path.relative_to(run).as_posix()
        return {'member': 'payload/' + (prefix + '/' if prefix else '') + relative,
                'sha256': file_sha(path)}
    return {'schema_version': 1, 'kind': 'archived-managed-run-summary',
            'reported_status': result['status'], 'scope': result.get('scope'),
            'profile': result['profile'], 'host': result['host'], 'target': result['target'],
            'acceptance_basis': 'Original archived inputs; packaging does not rerun verification.',
            'archive_sha256': record['sha256'], 'original_result': ref(run / 'result.json'),
            'input_fingerprints': {'before': ref(before), 'after': ref(after), 'equal': True},
            'audit': {k: v for k, v in audit.items() if k != 'files_sha256'},
            'original_audit': ref(run / 'audit/result.json'),
            'stages': {'native_tests': 'Separate observations in original run; not formal proof.',
                       'extraction_and_profile_checks': 'See original pipeline receipt and profile configuration.',
                       'lean_build_and_axiom_audit': 'passed', 'before_after_fingerprints': 'equal'},
            'sarif': 'Not a cargo-proofs recording result.'}


def check_publication(directory):
    """Check a distributed summary tree without requiring private local archives."""
    directory = Path(directory)
    record = json.loads((directory / 'archive.json').read_text())
    if (record['availability'] != 'local-only' or record['public_url'] is not None
            or record['archive'] != record['sha256'] + '.tar.gz'):
        raise ValueError('Invalid local archive descriptor')
    fixtures = json.loads((directory / 'fixtures.json').read_text())['files'] if (directory / 'fixtures.json').exists() else {}
    permitted = {'.gitignore', 'archive.json', 'summary.json', 'fixtures.json', 'README.md'} | set(fixtures)
    actual = inventory(directory)
    # Existing historical adapters import a pinned Python parser in place. Its
    # interpreter cache is ignored by Git and is not a distributed artifact.
    cache = {n for n in actual if '__pycache__' in PurePosixPath(n).parts and n.endswith('.pyc')}
    extra = set(actual) - permitted - cache
    if extra:
        raise ValueError('Unclassified evidence artifacts: ' + ', '.join(sorted(extra)))
    for name, expected in fixtures.items():
        safe_name(name)
        if name not in actual or any(actual[name][k] != expected[k] for k in ('sha256', 'bytes', 'mode')):
            raise ValueError('Missing or changed compatibility fixture: ' + name)
        if not expected.get('consumers'):
            raise ValueError('Fixture has no documented consumer: ' + name)
    summary = json.loads((directory / 'summary.json').read_text())
    if summary['archive_sha256'] != record['sha256']:
        raise ValueError('Summary/archive mismatch')
    return {'files': len(actual), 'compatibility_fixtures': len(fixtures)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    pack = sub.add_parser('archive')
    pack.add_argument('source', type=Path)
    pack.add_argument('--store', type=Path, required=True)
    pack.add_argument('--descriptor', type=Path, required=True)
    for command in ('verify', 'restore'):
        child = sub.add_parser(command)
        child.add_argument('descriptor', type=Path)
        child.add_argument('--store', type=Path, required=True)
        if command == 'restore':
            child.add_argument('--destination', type=Path, required=True)
    summary = sub.add_parser('summarize')
    summary.add_argument('run', type=Path)
    summary.add_argument('--descriptor', type=Path, required=True)
    summary.add_argument('--store', type=Path, required=True)
    summary.add_argument('--member-prefix', default='')
    summary.add_argument('--output', type=Path, required=True)
    check = sub.add_parser('check')
    check.add_argument('directory', type=Path)
    args = parser.parse_args()
    if args.command == 'check':
        check_publication(args.directory)
    elif args.command == 'archive':
        if args.descriptor.exists() or args.descriptor.resolve().is_relative_to(args.source.resolve()):
            raise ValueError('Descriptor must be new and outside the archived tree')
        write_json(args.descriptor, archive(args.source, args.store))
    else:
        record = json.loads(args.descriptor.read_text())
        if args.command == 'restore':
            restore(record, args.store, args.destination)
        else:
            files = verify(record, args.store)
            if args.command == 'summarize':
                for name, entry in inventory(args.run).items():
                    member = (args.member_prefix.rstrip('/') + '/' if args.member_prefix else '') + name
                    if files.get(member) != entry:
                        raise ValueError('Run differs from archived member: ' + member)
                write_json(args.output, summarize(args.run, record, args.member_prefix))
    print('OK:', args.command)


if __name__ == '__main__':
    main()
