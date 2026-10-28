"""Common orchestration. Local script logs are evidence, never SARIF input."""
import argparse
from contextlib import ExitStack, contextmanager
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import tomllib

from . import source, tools

SCRIPTS = Path(__file__).resolve().parents[1]
REPO = SCRIPTS.parent


def helper(name):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def profiles(root):
    data = tomllib.loads((root / 'aeneas/profiles.toml').read_text())
    if data['default'] not in data['profiles']:
        raise ValueError('Default profile is missing')
    return data


def configuration(root, name):
    data = profiles(root)
    entry = execution_entries(root)[name]
    profile = source.contained(root, entry['path'])
    config = json.loads((profile / 'verification.json').read_text())
    if config['schema_version'] != 1:
        raise ValueError('Unsupported verification config')
    return profile, config, entry


def execution_entries(root):
    """Public profiles may own separately built/audited subject units."""
    entries = {}
    import re
    for name, entry in profiles(root)['profiles'].items():
        entries[name] = entry
        for unit, settings in entry.get('units', {}).items():
            if not re.fullmatch(r'[a-z][a-z0-9-]*', unit):
                raise ValueError('Invalid proof unit name: ' + unit)
            entries[name + '/' + unit] = settings
    return entries


def execution_name(root, profile):
    matches = [name for name, entry in execution_entries(root).items()
               if source.contained(root, entry['path']) == profile]
    if len(matches) != 1:
        raise ValueError('Ambiguous or missing proof unit path: ' + str(profile))
    return matches[0]


def units(root, name):
    _, config, entry = configuration(root, name)
    selected = entry.get('units', {})
    if bool(selected) != (config.get('execution') == 'all-units'):
        raise ValueError('Composite profile must explicitly require all declared units')
    return [name + '/' + unit for unit in selected]


def dependencies(root, name):
    _, _, entry = configuration(root, name)
    for unit in units(root, name):
        yield root, unit
    for dep in entry.get('dependencies', []):
        if ':' in dep:
            crate, dep_name = dep.rsplit(':', 1)
            yield source.contained(REPO, crate), dep_name
        else:
            yield root, dep


def auxiliary_tools(profile, config):
    configured = config.get('auxiliary_tools', {})
    if not configured and (profile / 'ordinary/toolchain.lock.json').is_file():
        configured = {'ordinary': 'ordinary'}
    import re
    for alias, directory in configured.items():
        if not re.fullmatch(r'[a-z][a-z0-9_]*', alias):
            raise ValueError('Invalid auxiliary tool name')
        yield alias, source.contained(profile, directory)


@contextmanager
def operation_lock(root, name):
    roots, visited, active = set(), set(), set()
    def visit(crate, profile_name):
        key = (crate, profile_name)
        if key in active:
            raise ValueError('Cyclic profile dependency')
        if key in visited:
            return
        active.add(key)
        roots.add(crate)
        for child, child_name in dependencies(crate, profile_name):
            visit(child, child_name)
        active.remove(key)
        visited.add(key)
    visit(root, name)
    # All processes acquire the same order, including cross-crate dependencies.
    with ExitStack() as stack:
        for crate in sorted(roots):
            stack.enter_context(source.exclusive(crate / '.work/verify.lock'))
        yield


def validate_runtime_environment():
    """Refuse caller settings that silently change the locked verification input."""
    import re
    if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE', '') not in ('', '0'):
        raise ValueError('Verification requires Python assertions; unset PYTHONOPTIMIZE/-O')
    overrides = {'RUSTC', 'RUSTDOC', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER',
                 'CARGO_BUILD_RUSTC', 'CARGO_BUILD_RUSTDOC', 'CARGO_BUILD_RUSTC_WRAPPER',
                 'CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER', 'RUSTFLAGS', 'CARGO_ENCODED_RUSTFLAGS'}
    for name, value in os.environ.items():
        if value and (name in overrides or re.fullmatch(r'CARGO_TARGET_.+_RUSTFLAGS', name)):
            raise ValueError(f'Unpinned compiler override: {name}; configure semantic flags inside the locked profile')
    target = os.environ.get('CARGO_BUILD_TARGET')
    if target and target != tools.host():
        raise ValueError('CARGO_BUILD_TARGET differs from the supported native verification target')


def runtime_identity(lock):
    """Observe actual installed pinned runtimes on every before/after check, not at setup only."""
    env = os.environ.copy()
    identities = {'host': tools.host(), 'target': tools.host(), 'binaries': {}, 'cfg': {},
                  'build_context': tools.build_context()}
    def output(argv, process_env):
        return subprocess.check_output(argv, env=process_env).decode().strip()
    for role, channel in [('native', lock['native_rust']), ('extraction', lock['extraction_rust'])]:
        rust_env = dict(env, RUSTUP_TOOLCHAIN=channel)
        for name in ('rustc', 'cargo'):
            path = Path(output(['rustup', 'which', '--toolchain', channel, name], rust_env)).resolve(strict=True)
            identities['binaries'][role + '_' + name] = {
                'toolchain': channel, 'path': str(path), 'sha256': source.digest(path),
                'version': output([str(path), '-vV'], rust_env)}
            if name == 'rustc':
                identities['cfg'][role] = output([str(path), '--print', 'cfg', '--target', tools.host()], rust_env).splitlines()
    lean_env = dict(env, ELAN_TOOLCHAIN=lock['lean'])
    for name in ('lean', 'lake'):
        path = Path(output(['elan', 'which', name], lean_env)).resolve(strict=True)
        identities['binaries'][name] = {'toolchain': lock['lean'], 'path': str(path),
                                       'sha256': source.digest(path), 'version': output([str(path), '--version'], lean_env)}
    return identities


def fingerprint(root, profile, store, lock, active=None, runtimes=None):
    # Share observations only within one recursive snapshot, never across runs/checks.
    runtimes = {} if runtimes is None else runtimes
    active = set() if active is None else active
    name = execution_name(root, profile)
    identity = (str(root), name)
    if identity in active:
        raise ValueError('Cyclic fingerprint dependency')
    active.add(identity)
    result = {}
    names = subprocess.check_output(['git', '-C', str(REPO), 'ls-files', '--cached', '--others', '--exclude-standard', '-z', str(root.relative_to(REPO)), 'scripts']).split(b'\0')
    output_dirs = [source.contained(root, entry['path']) for entry in execution_entries(root).values()]
    for filename in names:
        if not filename:
            continue
        path = REPO / os.fsdecode(filename)
        output = any(path == p / 'results.md' or path.is_relative_to(p / 'evidence') for p in output_dirs)
        if path.is_file() and not path.is_symlink() and '.work' not in path.parts and not output:
            result[path.relative_to(REPO).as_posix()] = source.digest(path)
    result['toolchain'] = tools.check(store, lock)
    runtime_key = tuple(lock[k] for k in ('native_rust', 'extraction_rust', 'lean'))
    if runtime_key not in runtimes:
        runtimes[runtime_key] = runtime_identity(lock)
    result['runtime'] = runtimes[runtime_key]
    result['source'] = source.inventory(source.directory(root))
    lean = root / '.work/build' / name / tools.host() / 'proofs'
    result['lake_dependencies'] = check_lake(lean)
    _, config, _ = configuration(root, name)
    result['auxiliary_tools'] = {}
    for alias, auxiliary in auxiliary_tools(profile, config):
        auxiliary_lock, key = tools.identity(auxiliary)
        result['auxiliary_tools'][alias] = tools.check(REPO / '.work/tools' / key, auxiliary_lock)
    result['dependencies'] = {}
    for dep_root, dep_name in dependencies(root, name):
        dep_profile, _, _ = configuration(dep_root, dep_name)
        dep_lock, key = tools.identity(dep_profile)
        result['dependencies'][str(dep_root.relative_to(REPO)) + ':' + dep_name] = fingerprint(
            dep_root, dep_profile, REPO / '.work/tools' / key, dep_lock, active, runtimes)
    active.remove(identity)
    return result


def materialize(root, name, profile, store):
    dest = root / '.work/build' / name / tools.host() / 'proofs'
    dest.parent.mkdir(parents=True, exist_ok=True)
    if dest.exists():
        for child in dest.iterdir():
            if child.name != '.lake':
                shutil.rmtree(child) if child.is_dir() and not child.is_symlink() else child.unlink()
    shutil.copytree(profile / 'proofs', dest, dirs_exist_ok=True,
                    ignore=shutil.ignore_patterns('.lake', '.proofs-toolchain', '*.olean', '*.ilean'))
    backend = store / 'aeneas/backends/lean'
    file = dest / 'lakefile.toml'
    text = file.read_text().replace('@AENEAS_BACKEND@', str(backend)).replace('@TARGET@', tools.host()).replace('.proofs-toolchain/aeneas/backends/lean', str(backend))
    known = {'aeneas': backend}
    source_paths, identities, visited = {}, {}, set()
    def collect(crate, profile_name):
        for dep_root, dep_name in dependencies(crate, profile_name):
            if (dep_root, dep_name) in visited:
                continue
            visited.add((dep_root, dep_name))
            dep_profile, _, _ = configuration(dep_root, dep_name)
            origin = dep_profile / 'proofs'
            built = dep_root / '.work/build' / dep_name / tools.host() / 'proofs'
            package = tomllib.loads((origin / 'lakefile.toml').read_text())['name']
            if package in known and known[package] != built:
                raise ValueError('Conflicting dependency package: ' + package)
            known[package] = built
            source_paths[origin.resolve()] = built
            identities[str(dep_root.relative_to(REPO)) + ':' + dep_name] = built
            collect(dep_root, dep_name)
    collect(root, name)
    import re
    def dependency(match):
        identity = match.group(1)
        if identity not in identities:
            raise ValueError('Undeclared profile dependency: ' + identity)
        return str(identities[identity])
    text = re.sub(r'@DEPENDENCY:([^@]+)@', dependency, text)
    original = tomllib.loads((profile / 'proofs/lakefile.toml').read_text())
    for requirement in original.get('require', []):
        old = requirement.get('path')
        if not old or '@' in old:
            continue
        path = (profile / 'proofs' / old).resolve()
        if path not in source_paths:
            raise ValueError('Undeclared local Lake dependency: ' + old)
        text = text.replace('"' + old + '"', json.dumps(str(source_paths[path])))
    if not any(p['name'] == 'aeneas' for p in original.get('require', [])):
        text += '\n[[require]]\nname = "aeneas"\npath = ' + json.dumps(str(backend)) + '\n'
    file.write_text(text)
    manifest = dest / 'lake-manifest.json'
    if manifest.exists():
        data = json.loads(manifest.read_text())
        for package in data.get('packages', []):
            # Lake sometimes serializes a hyphenated Name with guillemets.
            original_name = package['name']
            normalized = original_name.removeprefix('«').removesuffix('»')
            if normalized in known:
                config_file = 'lakefile.lean' if normalized == 'aeneas' else 'lakefile.toml'
                package.clear()
                package.update({'name': original_name, 'type': 'path', 'dir': str(known[normalized]),
                                'manifestFile': 'lake-manifest.json', 'configFile': config_file,
                                'inherited': normalized not in {p['name'] for p in tomllib.loads(text).get('require', [])}})
            elif package.get('type') == 'path':
                raise ValueError('Unpinned inherited Lake path dependency: ' + original_name)
        source.write_json(manifest, data)
        donor = os.environ.get('AENEAS_LAKE_CACHE')
        if donor:
            packages = dest / '.lake/packages'
            packages.mkdir(parents=True, exist_ok=True)
            for package in data.get('packages', []):
                if package['type'] != 'git':
                    continue
                cached = Path(donor) / package['name']
                if not cached.exists() or (packages / package['name']).exists():
                    continue
                if tools.git(cached, 'rev-parse', 'HEAD') != package['rev']:
                    raise ValueError('Lake cache revision mismatch: ' + package['name'])
                if tools.git(cached, 'status', '--porcelain', '--untracked-files=no'):
                    raise ValueError('Dirty Lake dependency cache: ' + package['name'])
                (packages / package['name']).symlink_to(cached.resolve(), target_is_directory=True)
    return dest

def check_lake(lean):
    manifest = json.loads((lean / 'lake-manifest.json').read_text())
    identities = {}
    for package in manifest.get('packages', []):
        if package['type'] == 'git':
            path = lean / '.lake/packages' / str(source.relative(package['name']))
            if tools.git(path, 'rev-parse', 'HEAD') != package['rev']:
                raise ValueError('Lake dependency revision changed: ' + package['name'])
            if tools.git(path, 'status', '--porcelain', '--untracked-files=no'):
                raise ValueError('Modified Lake dependency: ' + package['name'])
            identities[package['name']] = package['rev']
    return {'packages': identities, 'manifest': source.digest(lean / 'lake-manifest.json'),
            'configuration': source.digest(lean / 'lakefile.toml')}


def prepare_lake(lean, offline):
    manifest = json.loads((lean / 'lake-manifest.json').read_text())
    with (lean.parent / 'lake-prepare.log').open('ab') as log:
        for package in manifest.get('packages', []):
            if package['type'] != 'git':
                continue
            path = lean / '.lake/packages' / str(source.relative(package['name']))
            if path.exists():
                continue
            if offline:
                raise ValueError('Offline Lake dependency missing: ' + package['name'])
            if not package['url'].startswith('https://'):
                raise ValueError('Lake dependency must use HTTPS')
            path.parent.mkdir(parents=True, exist_ok=True)
            tools.run(['git', 'init', path], lean, log)
            tools.run(['git', 'remote', 'add', 'origin', package['url']], path, log)
            tools.run(['git', 'fetch', '--depth=1', 'origin', package['rev']], path, log)
            tools.run(['git', 'checkout', '--detach', package['rev']], path, log)
            tools.run(['git', 'submodule', 'update', '--init', '--recursive'], path, log)
    check_lake(lean)


def native_surface(root):
    """Check semantic Cargo declarations; changed surfaces require explicit reasons."""
    outer = tomllib.loads((root / 'Cargo.toml').read_text())
    upstream = tomllib.loads((source.directory(root) / 'Cargo.toml').read_text())
    policy = json.loads((root / 'source.lock.json').read_text()).get('manifest_exceptions', {})
    differences = []
    for key in ('features', 'dependencies', 'dev-dependencies', 'build-dependencies', 'target'):
        if outer.get(key, {}) != upstream.get(key, {}) and not policy.get(key):
            differences.append(key)
    for key in ('name', 'version', 'edition', 'links', 'build'):
        default = '2015' if key == 'edition' else None
        if outer['package'].get(key, default) != upstream['package'].get(key, default) and not policy.get('package.' + key):
            differences.append('package.' + key)
    if differences:
        raise ValueError('Unreviewed manifest differences: ' + ', '.join(differences))
    outer_lib, release_lib = outer.get('lib', {}), upstream.get('lib', {})
    actual_path = (root / outer_lib.get('path', 'src/lib.rs')).resolve()
    expected_path = (source.directory(root) / release_lib.get('path', 'src/lib.rs')).resolve()
    if actual_path != expected_path:
        raise ValueError('Cargo library does not compile the locked release source')
    if ({k: v for k, v in outer_lib.items() if k != 'path'} !=
        {k: v for k, v in release_lib.items() if k != 'path'} and not policy.get('lib')):
        raise ValueError('Unreviewed library target configuration')


def check_aliases(root, lock):
    for name in lock.get('aliases', []):
        alias = root / source.relative(name)
        target = source.directory(root)
        if alias.is_symlink():
            if alias.resolve() != target.resolve():
                raise ValueError(f'Incorrect source alias: {alias}')
        elif alias.exists():
            raise ValueError(f'Legacy source still occupies {alias}; migrate explicitly first')
        else:
            alias.parent.mkdir(parents=True, exist_ok=True)
            alias.symlink_to(os.path.relpath(target, alias.parent), target_is_directory=True)


def shared_caches(root):
    # Explicitly selected disposable caches can be reused by isolated CLI checkouts.
    # Restored source trees remain version-local and are always independently checked.
    for variable, destination in [('AENEAS_TOOL_CACHE', REPO / '.work/tools'),
                                  ('AENEAS_ARCHIVE_CACHE', root / '.work/cache')]:
        value = os.environ.get(variable)
        if not value:
            continue
        target = Path(value)
        if not target.is_absolute():
            raise ValueError(variable + ' must be an absolute cache path')
        if destination.exists() or destination.is_symlink():
            if destination.resolve() != target.resolve():
                raise ValueError(variable + ' differs from existing cache; choose a fresh checkout or the existing cache')
            continue
        target.mkdir(parents=True, exist_ok=True)
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.symlink_to(target.resolve(), target_is_directory=True)


def prepare(root, name, offline=False, sources_only=False, active=None, prepared=None):
    active = set() if active is None else active
    prepared = {} if prepared is None else prepared
    identity = (str(root), name)
    if identity in active:
        raise ValueError('Cyclic profile dependency')
    if identity in prepared:
        return prepared[identity]
    active.add(identity)
    profile, config, entry = configuration(root, name)
    shared_caches(root)
    source.restore(root, offline=offline)
    lock = json.loads((root / 'source.lock.json').read_text())
    check_aliases(root, lock)
    native_surface(root)
    if sources_only:
        active.remove(identity)
        return None
    selected = units(root, name)
    if selected:
        for unit in selected:
            prepare(root, unit, offline, active=active, prepared=prepared)
        active.remove(identity)
        return None
    for dep_root, dep_name in dependencies(root, name):
        prepare(dep_root, dep_name, offline, active=active, prepared=prepared)
    store, lock = tools.prepare(root, profile, offline)
    for _, auxiliary in auxiliary_tools(profile, config):
        tools.prepare(root, auxiliary, offline)
    dest = materialize(root, name, profile, store)
    prepare_lake(dest, offline)
    for alias, path in [(root / '.work/selected-tools', store), (root / '.work/selected-proofs', dest)]:
        if alias.is_symlink():
            alias.unlink()
        elif alias.exists():
            raise ValueError(f'Expected managed symlink: {alias}')
        alias.symlink_to(os.path.relpath(path, alias.parent), target_is_directory=True)
    active.remove(identity)
    prepared[identity] = store, lock, dest
    return prepared[identity]


def commands(items, root, env, run_dir, prefix):
    for i, item in enumerate(items):
        if isinstance(item, list):
            argv, cwd = item, root
        else:
            argv = item['argv']
            cwd = root if item.get('cwd', '.') == '.' else source.contained(root, item['cwd'])
        with (run_dir / f'{prefix}-{i}.log').open('wb') as log:
            tools.run(argv, cwd, log, env)


def verify(root, name, offline=False, prepared=None):
    validate_runtime_environment()
    if units(root, name):
        return verify_units(root, name, offline)
    profile, config, _ = configuration(root, name)
    if config.get('migration_blockers'):
        raise ValueError('Profile migration incomplete: ' + '; '.join(config['migration_blockers']))
    if tools.host() not in config.get('supported_targets', [config.get('target')]):
        raise ValueError(f'Profile has no reviewed target configuration for {tools.host()}')
    store, lock, lean = prepare(root, name, offline, prepared=prepared)
    env = tools.environment(store, lock)
    env.update({'AENEAS_SOURCE': str(store / 'aeneas'), 'AENEAS_LEAN_BACKEND': str(store / 'aeneas/backends/lean'),
                'AENEAS_PROOF_DIR': str(lean), 'CARGO_TARGET_DIR': str(root / '.work/build/native' / tools.host()),
                'LAKE_NO_CACHE': 'true', 'LAKE_ARTIFACT_CACHE': 'false'})
    for alias, auxiliary in auxiliary_tools(profile, config):
        auxiliary_lock, key = tools.identity(auxiliary)
        auxiliary_store = REPO / '.work/tools' / key
        tools.check(auxiliary_store, auxiliary_lock)
        env['AENEAS_' + alias.upper() + '_SOURCE'] = str(auxiliary_store / 'aeneas')
        env['AENEAS_' + alias.upper() + '_BIN'] = str(auxiliary_store / 'aeneas/bin/aeneas')
    if offline:
        env['CARGO_NET_OFFLINE'] = 'true'
    runs = root / '.work/runs'
    runs.mkdir(parents=True, exist_ok=True)
    run_dir = Path(tempfile.mkdtemp(prefix=name.replace('/', '-') + '-', dir=runs))
    env['AENEAS_RUN_DIR'] = str(run_dir)
    print(f'Local evidence: {run_dir}', flush=True)
    status = {'status': 'failed', 'profile': name, 'host': tools.host(), 'target': tools.host()}
    try:
        before = fingerprint(root, profile, store, lock)
        source.write_json(run_dir / 'inputs-before.json', before)
        commands(config.get('native', []), root, env, run_dir, 'native')
        commands(config.get('additional_checks', []), root, env, run_dir, 'checks')
        for index, extraction in enumerate(config.get('extractions', [])):
            cfg = source.contained(profile, extraction['config'])
            cwd = root if extraction.get('cwd', '.') == '.' else source.contained(root, extraction['cwd'])
            extract_env = env.copy()
            extract_env['RUSTUP_TOOLCHAIN'] = lock['extraction_rust']
            if extraction.get('tool'):
                alias = extraction['tool'].upper()
                extract_env['PATH'] = str(Path(env['AENEAS_' + alias + '_BIN']).parent) + os.pathsep + env['PATH']
            output = run_dir / f'extraction-{index}'
            with (run_dir / f'extraction-{index}.log').open('wb') as log:
                tools.run([sys.executable, SCRIPTS / 'aeneas-extract.py', cwd, '--config', cfg, '--output', output], root, log, extract_env)
            expected = json.loads(cfg.read_text())['models']
            if set(expected) != set(extraction['models']):
                raise ValueError('Extraction comparison inventory is incomplete')
            for generated, maintained in extraction['models'].items():
                maintained = maintained.replace('@TARGET@', tools.host()).replace('.proofs-toolchain/aeneas/backends/lean', str(backend))
                if (output / generated).read_bytes() != source.contained(profile, maintained).read_bytes():
                    raise ValueError(f'Regenerated model differs: {generated}')
        with (run_dir / 'lean-clean.log').open('wb') as log:
            package = tomllib.loads((lean / 'lakefile.toml').read_text())['name']
            tools.run(['lake', 'clean', package], lean, log, env)
        with (run_dir / 'audit.log').open('wb') as log:
            tools.run([sys.executable, SCRIPTS / 'aeneas-audit.py', root, '--lean-dir', lean,
                       '--inventory', source.contained(profile, config['inventory']),
                       '--proofs-toml', source.contained(profile, config['report']),
                       '--output', run_dir / 'audit'], root, log, env)
        commands(config.get('post_checks', []), root, env, run_dir, 'post')
        source.check(source.directory(root), json.loads((root / 'source.lock.json').read_text()))
        after = fingerprint(root, profile, store, lock)
        source.write_json(run_dir / 'inputs-after.json', after)
        if before != after:
            raise ValueError('Verification inputs changed during run')
        status['status'] = 'passed'
        status['scope'] = 'Configured extraction comparisons and named theorem audit; native observations are separate'
    except Exception as error:
        status['error'] = str(error)
        raise
    finally:
        status['files_sha256'] = {p.relative_to(run_dir).as_posix(): source.digest(p) for p in run_dir.rglob('*') if p.is_file()}
        source.write_json(run_dir / 'result.json', status)
    return run_dir


def verify_units(root, name, offline=False):
    """A profile succeeds only after every unit's standard build/audit succeeds."""
    selected = units(root, name)
    # Prepare the entire dependency graph before the first input fingerprint.
    prepared = {}
    prepare(root, name, offline, prepared=prepared)
    runs = root / '.work/runs'
    runs.mkdir(parents=True, exist_ok=True)
    run_dir = Path(tempfile.mkdtemp(prefix=name + '-all-', dir=runs))
    status = {'status': 'failed', 'profile': name, 'host': tools.host(),
              'target': tools.host(), 'units': []}
    def snapshot():
        result = {}
        runtimes = {}
        for unit in selected:
            profile, _, _ = configuration(root, unit)
            lock, key = tools.identity(profile)
            result[unit] = fingerprint(root, profile, REPO / '.work/tools' / key, lock, runtimes=runtimes)
        return result
    print(f'Combined local evidence: {run_dir}', flush=True)
    try:
        before = snapshot()
        source.write_json(run_dir / 'inputs-before.json', before)
        for unit in selected:
            child = verify(root, unit, offline, prepared=prepared)
            result = child / 'result.json'
            if json.loads(result.read_text())['status'] != 'passed':
                raise ValueError('Proof unit did not pass: ' + unit)
            status['units'].append({'name': unit, 'result': str(result), 'sha256': source.digest(result)})
        after = snapshot()
        source.write_json(run_dir / 'inputs-after.json', after)
        if before != after:
            raise ValueError('Verification inputs changed during combined run')
        status['status'] = 'passed'
        status['scope'] = 'All configured units passed their separate standard Lake builds and theorem/axiom audits; native checks are separate observations'
    except Exception as error:
        status['error'] = str(error)
        raise
    finally:
        source.write_json(run_dir / 'result.json', status)
    return run_dir


def lint(root):
    source.validate_lock(json.loads((root / 'source.lock.json').read_text()))
    data = profiles(root)
    for name in execution_entries(root):
        profile, config, _ = configuration(root, name)
        if units(root, name):
            continue
        if not config.get('extractions') and not config.get('additional_checks'):
            raise ValueError(f'No extraction checks configured: {name}')
        for key in ('inventory', 'report'):
            source.contained(profile, config[key]).read_bytes()
        helper('aeneas-audit').validate(json.loads((profile / config['inventory']).read_text()),
                                       tomllib.loads((profile / config['report']).read_text()))
        if config.get('migration_blockers'):
            raise ValueError(f'{name}: unresolved migration blockers')
    print(f'Layout valid: {root} ({len(data["profiles"])} profiles)')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['setup', 'verify', 'doctor', 'lint', 'check-source'])
    parser.add_argument('root', type=Path)
    parser.add_argument('--profile')
    parser.add_argument('--unit', help='Select an internal subject unit of the chosen profile')
    parser.add_argument('--offline', action='store_true')
    parser.add_argument('--sources-only', action='store_true')
    args = parser.parse_args()
    root = args.root.resolve()
    name = args.profile or profiles(root)['default']
    if name not in profiles(root)['profiles']:
        raise ValueError('Unknown public profile: ' + name)
    if args.unit:
        name += '/' + args.unit
        configuration(root, name)
    if args.command == 'setup':
        with operation_lock(root, name):
            prepare(root, name, args.offline, args.sources_only)
    elif args.command == 'verify':
        with operation_lock(root, name):
            verify(root, name, args.offline)
    elif args.command == 'doctor':
        print(json.dumps(tools.doctor(), indent=2))
    elif args.command == 'check-source':
        source.check(source.directory(root), json.loads((root / 'source.lock.json').read_text()))
    else:
        lint(root)


if __name__ == '__main__':
    main()
