"""Restore exact tool source trees and build into isolated, host-specific stores."""
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import stat
import subprocess
import tempfile

from .source import contained, digest, exclusive, write_json


def host():
    pair = (platform.system(), platform.machine())
    supported = {('Darwin', 'arm64'): 'aarch64-apple-darwin',
                 ('Linux', 'x86_64'): 'x86_64-unknown-linux-gnu'}
    if pair not in supported:
        raise ValueError(f'Unsupported native host: {pair}')
    return supported[pair]


def run(args, cwd, log, env=None):
    log.write(('\n$ ' + repr([str(x) for x in args]) + '\n').encode())
    log.flush()
    subprocess.run([str(x) for x in args], cwd=cwd, env=env, stdout=log,
                   stderr=subprocess.STDOUT, check=True)


def git_read_environment():
    return dict(os.environ, GIT_OPTIONAL_LOCKS='0')


def git(path, *args):
    return subprocess.check_output(['git', '-C', str(path), *args], stderr=subprocess.PIPE,
                                   env=git_read_environment()).decode().strip()


def doctor():
    host()
    required = ['git', 'cargo', 'rustup', 'elan', 'opam', 'cc', 'pkg-config']
    missing = [x for x in required if not shutil.which(x)]
    if not (shutil.which('gmake') or shutil.which('make')):
        missing.append('GNU make')
    if missing:
        raise ValueError('Missing prerequisites: ' + ', '.join(missing))
    make = shutil.which('gmake') or shutil.which('make')
    if 'GNU Make' not in subprocess.check_output([make, '--version']).decode():
        raise ValueError('GNU Make is required (install gmake on macOS)')
    if subprocess.run(['pkg-config', '--exists', 'gmp'], capture_output=True).returncode:
        raise ValueError('GMP development files are required (pkg-config gmp)')
    return {'host': host(), 'python': platform.python_version(),
            'cc': subprocess.check_output(['cc', '--version']).decode().splitlines()[0]}


def build_context():
    flags = ('SDKROOT', 'MACOSX_DEPLOYMENT_TARGET', 'CFLAGS', 'CPPFLAGS', 'CXXFLAGS',
             'LDFLAGS', 'RUSTFLAGS', 'CARGO_ENCODED_RUSTFLAGS', 'OCAMLPARAM', 'MAKEFLAGS')
    context = {'host': host(), 'recipe_sha256': digest(__file__),
               'cc': subprocess.check_output(['cc', '--version']).decode(),
               'flags': {name: os.environ.get(name) for name in flags}}
    if platform.system() == 'Darwin':
        context['sdk'] = subprocess.check_output(['xcrun', '--show-sdk-version']).decode().strip()
        context['sdk_path'] = subprocess.check_output(['xcrun', '--show-sdk-path']).decode().strip()
    return context


def identity(profile):
    lock_path = profile / 'toolchain.lock.json'
    lock = json.loads(lock_path.read_text())
    if lock.get('schema_version') != 1 or lock.get('recipe') != 'aeneas-opam-v1':
        raise ValueError('Unsupported toolchain lock')
    if digest(profile / 'opam.locked') != lock['opam_sha256']:
        raise ValueError('OCaml dependency lock changed')
    for tool in lock['repositories'].values():
        for patch in tool.get('patches', []):
            if digest(contained(profile, patch['file'])) != patch['sha256']:
                raise ValueError('Tool patch checksum mismatch')
    payload = {'lock': digest(lock_path), 'build_context': build_context(),
               'recipe_compatibility_sha256': digest(Path(__file__).with_name('recipe-compatibility.json'))}
    return lock, hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()



def check_tracked_blobs(checkout):
    """Read actual bytes/modes; Git index optimization flags are not trust inputs."""
    checkout = Path(checkout)
    entries = subprocess.check_output(['git', '-C', str(checkout), 'ls-files', '--stage', '-z'],
                                      env=git_read_environment()).split(b'\0')
    for entry in entries:
        if not entry:
            continue
        metadata, raw_path = entry.split(b'\t', 1)
        mode, expected, stage = metadata.split()
        relative = Path(os.fsdecode(raw_path))
        if stage != b'0' or relative.is_absolute() or '..' in relative.parts:
            raise ValueError('Invalid tracked source index entry')
        if mode == b'160000':
            # Aeneas/Charon is checked separately with its own lock, which may
            # include intentional patches. Other gitlinks retain their prior scope.
            continue
        parent = checkout
        for part in relative.parts[:-1]:
            parent = parent / part
            if parent.is_symlink():
                raise ValueError(f'Tracked source parent became a symlink: {relative}')
        path = checkout / relative
        attributes = path.lstat()
        if mode in (b'100644', b'100755'):
            if not stat.S_ISREG(attributes.st_mode):
                raise ValueError(f'Tracked source is not a regular file: {relative}')
            if bool(attributes.st_mode & 0o111) != (mode == b'100755'):
                raise ValueError(f'Tracked executable mode changed: {relative}')
            payload = path.read_bytes()
        elif mode == b'120000':
            if not stat.S_ISLNK(attributes.st_mode):
                raise ValueError(f'Tracked source is not a symlink: {relative}')
            payload = os.fsencode(os.readlink(path))
        else:
            raise ValueError(f'Unsupported tracked source mode: {mode!r}')
        actual = hashlib.sha1(b'blob ' + str(len(payload)).encode() + b'\0' + payload).hexdigest().encode()
        if len(expected) != 40 or actual != expected:
            raise ValueError(f'Tracked source blob changed: {relative}')


def source_check(checkout, spec):
    if git(checkout, 'remote', 'get-url', 'origin') != spec['url']:
        raise ValueError('Tool repository origin changed')
    if git(checkout, 'rev-parse', 'HEAD') != spec['revision']:
        raise ValueError('Tool base revision changed')
    index = subprocess.run(['git', '-C', str(checkout), 'diff', '--cached', '--quiet', '--ignore-submodules=none',
                            spec['tree'], '--'], capture_output=True, env=git_read_environment())
    if index.returncode:
        raise ValueError('Tool patched index differs from locked tree')
    check_tracked_blobs(checkout)
    # Nested repositories may have independently locked patches. The cached diff
    # above still checks their gitlink entries against the exact parent tree.
    subprocess.run(['git', '-C', str(checkout), 'diff', '--quiet', '--ignore-submodules=all', '--'],
                   check=True, env=git_read_environment())
    if git(checkout, 'ls-files', '--others', '--exclude-standard'):
        raise ValueError(f'Untracked tool source files: {checkout}')


def restore_repository(path, spec, profile, log, offline):
    if not path.exists():
        # A local Git object cache can seed a build, but never changes identity checks.
        seed = os.environ.get('AENEAS_GIT_CACHE') if spec['url'].endswith('/aeneas.git') else None
        bootstrap = os.environ.get('AENEAS_BOOTSTRAP_ROOT')
        if bootstrap:
            suffix = {'https://github.com/AeneasVerif/aeneas.git': 'aeneas',
                      'https://github.com/AeneasVerif/charon.git': 'aeneas/charon',
                      'https://github.com/proofs-rs/proofs-rs.git': 'proofs-rs'}.get(spec['url'])
            candidate = Path(bootstrap) / suffix if suffix else None
            if candidate and candidate.exists():
                seed = str(candidate)
        if spec['url'] == 'https://github.com/proofs-rs/proofs-rs.git' and os.environ.get('AENEAS_PROOFS_RS_CACHE'):
            seed = os.environ['AENEAS_PROOFS_RS_CACHE']
        if offline and not seed:
            raise ValueError(f"Offline tool cache miss: {spec['url']}")
        run(['git', 'clone', '--no-checkout', seed or spec['url'], path], profile, log)
        run(['git', 'remote', 'set-url', 'origin', spec['url']], path, log)
        run(['git', 'checkout', '--detach', spec['revision']], path, log)
        for patch in spec.get('patches', []):
            patch_path = contained(profile, patch['file'])
            run(['git', 'apply', '--index', '--check', patch_path], path, log)
            run(['git', 'apply', '--index', patch_path], path, log)
        # A newly patched index need not have a corresponding tree object yet.
        # Materialize it exactly once while setup owns this private new checkout;
        # all checks of existing/shared checkouts remain strictly read-only.
        if git(path, 'write-tree') != spec['tree']:
            raise ValueError('Restored patch tree differs from locked tree')
    source_check(path, spec)


def paths(store):
    return {'aeneas': store / 'aeneas/bin/aeneas',
            'charon': store / 'aeneas/charon/bin/charon',
            'charon-driver': store / 'aeneas/charon/bin/charon-driver',
            'cargo-proofs': store / 'cargo-proofs/bin/cargo-proofs'}


def check(store, lock):
    receipt = json.loads((store / 'receipt.json').read_text())
    if receipt.get('identity') != store.name:
        raise ValueError('Tool receipt cache identity differs from its store')
    if receipt.get('inputs') != lock:
        raise ValueError('Tool receipt inputs differ from supplied lock')
    for name, spec in lock['repositories'].items():
        source_check(store / ('aeneas/charon' if name == 'charon' else name), spec)
    for name, path in paths(store).items():
        if digest(path) != receipt['binaries'][name]:
            raise ValueError(f'Tool binary changed: {name}')
    return receipt


def environment(store, lock):
    env = os.environ.copy()
    # Preserve caller homes; choose explicit tool paths and toolchain per subprocess.
    env['PATH'] = os.pathsep.join([str(store / 'aeneas/bin'), str(store / 'aeneas/charon/bin'),
                                 str(store / 'cargo-proofs/bin'), env.get('PATH', '')])
    env['RUSTUP_TOOLCHAIN'] = lock['native_rust']
    env['AENEAS_EXTRACT_RUST'] = lock['extraction_rust']
    env['AENEAS_NATIVE_TOOLCHAIN'] = lock['native_rust']
    env['ELAN_TOOLCHAIN'] = lock['lean']
    return env



def compiler_context_compatibility(previous, current):
    """Allow only a reviewed one-way recipe transition, with identical build inputs.

    This applies solely to verified compiler component reuse. It never changes a
    store's identity, rewrites an old receipt or authorizes a missing offline build.
    """
    if not isinstance(previous, dict) or current.get('recipe_sha256') != digest(__file__):
        return None
    old_recipe, new_recipe = previous.get('recipe_sha256'), current.get('recipe_sha256')
    if not isinstance(old_recipe, str) or not re.fullmatch(r'[0-9a-f]{64}', old_recipe):
        return None
    if previous == current:
        return {'kind': 'identical-build-context', 'previous_recipe_sha256': old_recipe,
                'current_recipe_sha256': new_recipe}
    if ({k: v for k, v in previous.items() if k != 'recipe_sha256'} !=
            {k: v for k, v in current.items() if k != 'recipe_sha256'}):
        return None
    path = Path(__file__).with_name('recipe-compatibility.json')
    mapping = json.loads(path.read_text())
    if mapping.get('schema_version') != 1:
        raise ValueError('Unsupported recipe compatibility schema')
    entry = mapping.get('compiler_reuse', {}).get(old_recipe)
    if not isinstance(entry, dict) or entry.get('current_recipe_sha256') != new_recipe:
        return None
    return {'kind': 'reviewed-recipe-transition', 'previous_recipe_sha256': old_recipe,
            'current_recipe_sha256': new_recipe, 'reason': entry['reason'],
            'mapping_sha256': digest(path)}


def compiler_reuse_record(candidate, compatibility, components):
    return {'store': candidate.parent.name, 'receipt_sha256': digest(candidate),
            'components': components, **compatibility}


def prepare(root, profile, offline=False):
    doctor_info = doctor()
    lock, key = identity(profile)
    context = build_context()
    # Shared disposable cache, never another crate's tool directory.
    work = Path(__file__).resolve().parents[2] / '.work'
    store = work / 'tools' / key
    with exclusive(work / 'tools' / (key + '.lock')):
        if (store / 'receipt.json').exists():
            check(store, lock)
            return store, lock
        if offline:
            raise ValueError('Offline tool build unavailable; run setup once online')
        # Failed builds are retained for diagnosis, never silently resumed as valid.
        if store.exists():
            raise ValueError(f'Incomplete tool build: inspect and remove {store}')
        store.mkdir(parents=True)
        with (store / 'setup.log').open('wb') as log:
            reused = None
            charon_cache = None
            compiler_provenance = None
            charon_provenance = None
            for candidate in sorted((work / 'tools').glob('*/receipt.json')):
                previous = json.loads(candidate.read_text())
                old = previous.get('inputs', {})
                keys = ('recipe', 'native_rust', 'extraction_rust', 'lean', 'opam_sha256')
                compatibility = compiler_context_compatibility(previous.get('build_context'), context)
                compatible = (all(old.get(k) == lock[k] for k in keys)
                              and compatibility is not None)
                if compatible and old.get('repositories', {}).get('charon') == lock['repositories']['charon']:
                    check(candidate.parent, old)
                    charon_cache = candidate.parent / 'aeneas/charon'
                    charon_provenance = compiler_reuse_record(candidate, compatibility, ['charon'])
                if compatible and all(old.get('repositories', {}).get(n) == lock['repositories'][n] for n in ('aeneas', 'charon')):
                    (store / 'aeneas').symlink_to(candidate.parent / 'aeneas', target_is_directory=True)
                    reused = candidate.parent
                    compiler_provenance = compiler_reuse_record(candidate, compatibility, ['aeneas', 'charon'])
                    break
            for name in ('aeneas', 'charon', 'proofs-rs'):
                path = store / ('aeneas/charon' if name == 'charon' else name)
                if name == 'charon' and charon_cache and not path.exists():
                    path.symlink_to(charon_cache, target_is_directory=True)
                restore_repository(path, lock['repositories'][name], profile, log, offline)
            aeneas = store / 'aeneas'
            if (aeneas / 'charon-pin').read_text().strip().splitlines()[-1] != lock['repositories']['charon']['revision']:
                raise ValueError('Charon pin incompatible with Aeneas')
            env = os.environ.copy()
            env.pop('RUSTUP_TOOLCHAIN', None)
            switch = os.environ.get('AENEAS_REUSE_OPAM_SWITCH')
            if reused:
                log.write(f'Reused verified compiler build: {reused.name}\n'.encode())
            elif switch:
                check_opam(profile / 'opam.locked', switch, env)
            else:
                env['OPAMROOT'] = str(store / 'opam-root')
                switch = store / 'ocaml'
                run(['opam', 'init', '--bare', '--disable-sandboxing', '--no-setup', '-y'], store, log, env)
                run(['opam', 'switch', 'create', switch, '--empty', '-y'], store, log, env)
                run(['opam', 'switch', 'import', profile / 'opam.locked', '--switch', switch, '-y'], store, log, env)
                check_opam(profile / 'opam.locked', switch, env)
            for channel in (lock['native_rust'], lock['extraction_rust']):
                installed = subprocess.run(['rustup', 'run', channel, 'rustc', '--version'], capture_output=True, env=env)
                if installed.returncode:
                    run(['rustup', 'toolchain', 'install', channel, '--profile', 'minimal'], store, log, env)
            components = subprocess.check_output(['rustup', 'component', 'list', '--toolchain', lock['extraction_rust'], '--installed'], env=env).decode()
            for component in ('rustc-dev', 'llvm-tools', 'rust-src'):
                if not any(line.split()[0] == component or line.startswith(component + '-') for line in components.splitlines()):
                    run(['rustup', 'component', 'add', '--toolchain', lock['extraction_rust'], component], store, log, env)
            if lock['lean'] not in subprocess.check_output(['elan', 'toolchain', 'list'], env=env).decode():
                run(['elan', 'toolchain', 'install', lock['lean']], store, log, env)
            make = shutil.which('gmake') or shutil.which('make')
            if not reused:
                if not charon_cache:
                    run(['git', 'submodule', 'update', '--init', '--recursive'], aeneas / 'charon', log, env)
                    run([make, 'build-dev-charon-rust', 'charon-ml/src/CharonVersion.ml'], aeneas / 'charon', log, env)
                run(['opam', 'exec', '--switch', switch, '--', make], aeneas, log, env)
            run(['cargo', '+' + lock['native_rust'], 'install', '--path', store / 'proofs-rs/cli',
                 '--locked', '--root', store / 'cargo-proofs'], store, log, env)
            for name, spec in lock['repositories'].items():
                source_check(store / ('aeneas/charon' if name == 'charon' else name), spec)
            write_json(store / 'receipt.json', {'schema_version': 1, 'identity': key, **doctor_info,
                       'inputs': lock, 'build_context': context, 'compiler_cache': reused.name if reused else None,
                       'compiler_reuse': compiler_provenance or charon_provenance,
                       'binaries': {name: digest(p) for name, p in paths(store).items()}})
        return store, lock


def check_opam(path, switch, env):
    """An explicitly reused switch is read-only and must match every locked package."""
    installed = re.search(r'installed:\s*\[(.*?)\]', path.read_text(), re.S)
    if not installed:
        raise ValueError('Missing installed package set in opam.locked')
    expected = sorted(re.findall(r'"([^"]+)"', installed.group(1)))
    output = subprocess.check_output(['opam', 'list', '--switch', str(switch), '--installed',
                                      '--columns=name,version', '--short'], env=env).decode()
    actual = sorted('.'.join(line.split()) for line in output.splitlines() if line.strip())
    if actual != expected:
        raise ValueError('OCaml package set differs from opam.locked')
