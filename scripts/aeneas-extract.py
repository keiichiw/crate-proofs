#!/usr/bin/env python3
"""Extract selected local Rust bodies; this does not prove their correctness."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path


def extract(root, config_path, output):
    root, config_path, output = map(lambda p: Path(p).resolve(), (root, config_path, output))
    raw = config_path.read_bytes()
    config = json.loads(raw)
    entries, models = config['entries'], config['models']
    if not entries or any(not re.fullmatch(r'crate::[A-Za-z_0-9:]+', e) for e in entries):
        raise ValueError('entries must be nonempty local crate:: paths')
    impl_entries = config.get('impl_entries', [])
    if not isinstance(impl_entries, list) or any(
        not isinstance(e, str) or not re.fullmatch(
            r'\{impl crate::[A-Za-z_][A-Za-z_0-9]*(?:::[A-Za-z_][A-Za-z_0-9]*)* for (?:_|(?:core|alloc|std)(?:::[A-Za-z][A-Za-z_0-9]*)+)\}::[A-Za-z_][A-Za-z_0-9]*', e)
        for e in impl_entries
    ):
        raise ValueError('impl_entries must select methods of explicit local crate traits')
    ident_path = r'[A-Za-z][A-Za-z_0-9]*(?:::[A-Za-z][A-Za-z_0-9]*)*'
    foreign_impl_entries = config.get('foreign_impl_entries', [])
    if not isinstance(foreign_impl_entries, list) or any(
        not isinstance(e, str) or not re.fullmatch(
            rf'\{{impl (?:core|alloc|std)::{ident_path} for crate::{ident_path}\}}::[A-Za-z][A-Za-z_0-9]*', e)
        for e in foreign_impl_entries
    ):
        raise ValueError('foreign_impl_entries must select an exact standard trait method on a concrete local type')
    if not models or any(Path(p).is_absolute() or '..' in Path(p).parts or not p.endswith('.lean') for p in models):
        raise ValueError('models must name relative .lean output paths')
    for names in models.values():
        if not names or any(not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', n) for n in names):
            raise ValueError('each model requires nonempty Lean definition names')
    llbc = config['llbc']
    if Path(llbc).name != llbc or not llbc.endswith('.llbc'):
        raise ValueError('llbc must be a filename ending in .llbc')
    cargo_args = config.get('cargo_args', ['--lib', '--locked'])
    if not isinstance(cargo_args, list) or not all(isinstance(s, str) for s in cargo_args) or '--locked' not in cargo_args:
        raise ValueError('cargo_args must be an argument list including --locked')
    includes = config.get('charon_include', [])
    if not isinstance(includes, list) or any(
        not isinstance(s, str) or not re.fullmatch(r'(?:core|alloc|std)::[A-Za-z_0-9:]+', s)
        for s in includes
    ):
        raise ValueError('charon_include must contain explicit standard-library paths')
    # Opaque standard-library calls must resolve to reviewed backend models.
    # This selects concrete symbols only; generated axioms remain forbidden.
    ident = r'[A-Za-z][A-Za-z_0-9]*'
    std_path = rf'(?:core|alloc|std)(?:::{ident})+'
    opaque_symbol = rf'(?:{std_path}|{std_path}::\{{impl {std_path}(?: for {std_path})?\}}::{ident}|{std_path}::\{{{std_path}\}}::{ident})'
    opaques = config.get('charon_opaque', [])
    if not isinstance(opaques, list) or any(
        not isinstance(s, str) or not re.fullmatch(opaque_symbol, s)
        for s in opaques
    ):
        raise ValueError('charon_opaque must contain concrete standard-library symbols without wildcards')
    extract_opaque = config.get('extract_opaque_bodies', False)
    if not isinstance(extract_opaque, bool):
        raise ValueError('extract_opaque_bodies must be boolean')
    if opaques and extract_opaque:
        raise ValueError('charon_opaque cannot be combined with extract_opaque_bodies')
    dependency_args = [a for path in includes for a in ('--include', path)]
    dependency_args.extend(a for path in opaques for a in ('--opaque', path))
    if extract_opaque:
        dependency_args.append('--extract-opaque-bodies')
    output.mkdir(parents=True, exist_ok=False)
    commands = [
        ['charon', 'cargo', '--preset=aeneas', *[a for e in entries + impl_entries + foreign_impl_entries for a in ('--start-from', e)],
         *dependency_args,
         '--dest-file', str(output / llbc), '--', *cargo_args],
        ['aeneas', '-backend', 'lean', '-dest', str(output), str(output / llbc)],
    ]
    for label, command in zip(('charon', 'aeneas'), commands):
        with (output / f'{label}.log').open('w') as log:
            subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT, check=True)
    actual = {str(p.relative_to(output)) for p in output.rglob('*.lean')}
    if actual != set(models):
        raise ValueError(f'generated model inventory mismatch: {actual} != {set(models)}')
    for filename, definitions in models.items():
        source = (output / filename).read_text()
        if re.search(r'(?m)^\s*(?:axiom|opaque|partial\s+def)\b|\b(?:sorry|admit)\b', source):
            raise ValueError(f'unsupported or incomplete generated model: {filename}')
        for name in definitions:
            if not re.search(rf'(?m)^\s*def\s+{re.escape(name)}(?=\s|\(|:)', source):
                raise ValueError(f'missing definition {name} in {filename}')
    if config_path.read_bytes() != raw:
        raise ValueError('extraction config changed during execution')
    result = {'status': 'extracted-not-proved', 'commands': commands,
              'config_sha256': hashlib.sha256(raw).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'files_sha256': {str(p.relative_to(output)): hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in sorted(output.rglob('*')) if p.is_file()}}
    (output / 'extraction.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'Extracted (not proved): {output}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('project', type=Path)
    parser.add_argument('--config', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True, help='New directory; existing paths are refused')
    args = parser.parse_args()
    extract(args.project, args.config, args.output)


if __name__ == '__main__':
    main()
