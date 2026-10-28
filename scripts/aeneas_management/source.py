"""Restore immutable sources without adding upstream code to Git."""
from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import tarfile
import tempfile
import urllib.request


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def relative(value):
    p = PurePosixPath(value)
    if not value or p.is_absolute() or '..' in p.parts or '\\' in value or str(p) != value:
        raise ValueError(f'Unsafe relative path: {value!r}')
    return p


def contained(root, value):
    relative(value)
    root = Path(root).resolve()
    path = root.joinpath(value)
    if not path.resolve().is_relative_to(root):
        raise ValueError(f'Path escapes root: {value}')
    return path


@contextmanager
def exclusive(path):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('a') as stream:
        fcntl.flock(stream, fcntl.LOCK_EX)
        yield


def inventory(root):
    result = {}
    for p in sorted(Path(root).rglob('*')):
        if p.is_symlink():
            raise ValueError(f'Symlink in source: {p}')
        if p.is_file():
            result[p.relative_to(root).as_posix()] = {
                'sha256': digest(p), 'executable': bool(p.stat().st_mode & 0o111)}
        elif not p.is_dir():
            raise ValueError(f'Unsupported source entry: {p}')
    return result


def validate_lock(lock):
    if lock.get('schema_version') != 1 or lock.get('kind') not in ('registry', 'git'):
        raise ValueError('Unsupported source lock schema or kind')
    if not re.fullmatch(r'[A-Za-z0-9_-]+', lock['name']):
        raise ValueError('Invalid crate name')
    if not re.fullmatch(r'[A-Za-z0-9.+_-]+', lock['version']):
        raise ValueError('Invalid crate version')
    if not lock['files']:
        raise ValueError('Empty source inventory')
    for name, item in lock['files'].items():
        relative(name)
        if not re.fullmatch('[0-9a-f]{64}', item['sha256']) or type(item['executable']) is not bool:
            raise ValueError('Invalid source inventory entry')
    if lock['kind'] == 'registry':
        expected = f"https://static.crates.io/crates/{lock['name']}/{lock['name']}-{lock['version']}.crate"
        if lock['url'] != expected or not re.fullmatch('[0-9a-f]{64}', lock['sha256']):
            raise ValueError('Invalid crates.io archive identity')
    else:
        if not lock['url'].startswith('https://') or not re.fullmatch('[0-9a-f]{40}', lock['commit']):
            raise ValueError('Git source requires HTTPS and a full commit')
        if lock.get('subdirectory'):
            relative(lock['subdirectory'])


def check(root, lock):
    validate_lock(lock)
    actual = inventory(root)
    if actual != lock['files']:
        missing = sorted(set(lock['files']) - set(actual))
        extra = sorted(set(actual) - set(lock['files']))
        changed = sorted(k for k in actual.keys() & lock['files'].keys() if actual[k] != lock['files'][k])
        raise ValueError(f'Source differs from lock: missing={missing[:8]}, extra={extra[:8]}, changed={changed[:8]}')


def extract_archive(archive, destination, prefix):
    seen = set()
    total = 0
    with tarfile.open(archive, 'r:*') as tar:
        for member in tar:
            name = relative(member.name.rstrip('/'))
            if name.parts[0] != prefix:
                raise ValueError('Unexpected archive prefix')
            if member.isdir():
                continue
            if not member.isfile() or len(name.parts) < 2:
                raise ValueError('Only regular archive files are supported')
            rel = '/'.join(name.parts[1:])
            if rel in seen:
                raise ValueError('Duplicate archive member')
            seen.add(rel)
            total += member.size
            if total > 512 * 1024 * 1024:
                raise ValueError('Expanded archive exceeds 512 MiB')
            path = contained(destination, rel)
            path.parent.mkdir(parents=True, exist_ok=True)
            with tar.extractfile(member) as src, path.open('xb') as dst:
                shutil.copyfileobj(src, dst)
            path.chmod(0o755 if member.mode & 0o111 else 0o644)


def download(url, destination):
    request = urllib.request.Request(url, headers={'User-Agent': 'crate-proofs-source-manager/1'})
    with urllib.request.urlopen(request, timeout=60) as src, Path(destination).open('wb') as dst:
        if not src.url.startswith('https://'):
            raise ValueError('Download redirected away from HTTPS')
        size = 0
        while block := src.read(1024 * 1024):
            size += len(block)
            if size > 128 * 1024 * 1024:
                raise ValueError('Archive exceeds 128 MiB')
            dst.write(block)


def restore(root, *, offline=False, cache=None):
    root = Path(root).resolve()
    lock = json.loads((root / 'source.lock.json').read_text())
    validate_lock(lock)
    work = root / '.work'
    work.mkdir(exist_ok=True)
    cache = Path(cache) if cache else work / 'cache'
    cache.mkdir(parents=True, exist_ok=True)
    target = work / 'source'
    with exclusive(work / 'source.lock'):
        if target.exists():
            check(target, lock)
            return target
        with tempfile.TemporaryDirectory(prefix='source-', dir=work) as temp:
            stage = Path(temp) / 'source'
            stage.mkdir()
            if lock['kind'] == 'registry':
                archive = cache / (lock['sha256'] + '.crate')
                with exclusive(cache / (lock['sha256'] + '.lock')):
                    if not archive.exists():
                        if offline:
                            raise ValueError(f'Offline cache miss: {archive.name}')
                        incoming = Path(temp) / 'download.crate'
                        download(lock['url'], incoming)
                        if digest(incoming) != lock['sha256']:
                            raise ValueError('Archive checksum mismatch')
                        shutil.copyfile(incoming, archive.with_suffix('.partial'))
                        archive.with_suffix('.partial').replace(archive)
                    if digest(archive) != lock['sha256']:
                        raise ValueError('Corrupt archive cache')
                extract_archive(archive, stage, f"{lock['name']}-{lock['version']}")
            else:
                key = hashlib.sha256((lock['url'] + lock['commit']).encode()).hexdigest()
                repository = cache / (key + '.git')
                with exclusive(cache / (key + '.lock')):
                    if not repository.exists():
                        if offline:
                            raise ValueError('Offline Git cache miss')
                        subprocess.run(['git', 'init', '--bare', str(repository)], check=True, capture_output=True)
                    found = subprocess.run(['git', '-C', str(repository), 'cat-file', '-e', lock['commit'] + '^{commit}'], capture_output=True)
                    if found.returncode:
                        if offline:
                            raise ValueError('Offline Git commit missing')
                        subprocess.run(['git', '-C', str(repository), 'fetch', '--no-tags', lock['url'], lock['commit']], check=True, capture_output=True)
                    tree = lock['commit'] + (':' + lock['subdirectory'] if lock.get('subdirectory') else '')
                    entries = subprocess.check_output(['git', '-C', str(repository), 'ls-tree', '-r', tree])
                    if any(line.startswith((b'160000 ', b'120000 ')) for line in entries.splitlines()):
                        raise ValueError('Git source with submodules or symlinks requires explicit support')
                    archive = Path(temp) / 'git.tar'
                    with archive.open('wb') as out:
                        subprocess.run(['git', '-C', str(repository), 'archive', '--prefix=source/', tree], stdout=out, check=True)
                    extract_archive(archive, stage, 'source')
            check(stage, lock)
            stage.rename(target)
    return target
