#!/usr/bin/env python3
"""Build and audit named Lean theorems. Does not establish Rust/model correspondence."""
import argparse
import hashlib
import json
import re
import subprocess
import tomllib
from collections import defaultdict
from pathlib import Path

IDENT = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*')


def validate(inventory, report=None):
    checked = inventory['checked']
    if not checked or len({x['name'] for x in checked}) != len(checked):
        raise ValueError('empty or duplicate theorem inventory')
    for item in checked:
        if not all(IDENT.fullmatch(item[k]) for k in ('name', 'module')):
            raise ValueError('invalid Lean theorem or module name')
    mappings = inventory.get('recorder_mappings', [])
    by_name = {x['name']: x for x in checked}
    if len({(m['api'], m['theorem']) for m in mappings}) != len(mappings) or len({m['theorem'] for m in mappings}) != len(mappings):
        raise ValueError('duplicate API/theorem mapping')
    for m in mappings:
        if m['theorem'] not in by_name:
            raise ValueError('mapped theorem is not audited')
    if report is not None:
        actual = report['tool']['proofs']
        if [{'api': p['api'], 'theorem': p['theorem']} for p in actual] != mappings:
            raise ValueError('proofs.toml mappings differ from inventory')
        for p in actual:
            item = by_name[p['theorem']]
            if p['module'] != item['module'] or p.get('precondition') != item.get('precondition', 'true'):
                raise ValueError('mapped module/precondition differs from inventory')
    return checked


def audit_source(module, names):
    refs = ', '.join('`' + n for n in names)
    return f'''import Lean
import {module}
open Lean Elab Command
run_cmd do
  for theoremName in ([{refs}] : List Name) do
    match (← getEnv).find? theoremName with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Expected a theorem: {{theoremName}}"
    let axioms ← Lean.collectAxioms theoremName
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Disallowed axiom in {{theoremName}}: {{ax}}"
    liftIO <| IO.println s!"AUDIT OK: {{theoremName}}"
'''


def fingerprints(project, lean, inventory, report):
    files = [inventory, Path(__file__).resolve()]
    if report:
        files.append(report)
    files += [p for p in lean.rglob('*') if p.is_file() and '.lake' not in p.relative_to(lean).parts
              and (p.suffix in ('.lean', '.toml', '.json') or p.name == 'lean-toolchain')]
    return {str(p.resolve()): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(files))}


def audit(project, inventory_path, lean_dir, output, report_path=None):
    project, inventory_path, output = map(lambda p: Path(p).resolve(), (project, inventory_path, output))
    lean = (project / lean_dir).resolve()
    report_path = Path(report_path).resolve() if report_path else None
    inventory = json.loads(inventory_path.read_text())
    report = tomllib.loads(report_path.read_text()) if report_path else None
    checked = validate(inventory, report)
    if output == lean or lean in output.parents:
        raise ValueError('audit output must be outside the Lean source directory')
    groups = defaultdict(list)
    for item in checked:
        groups[item['module']].append(item['name'])
    output.mkdir(parents=True, exist_ok=False)
    before = fingerprints(project, lean, inventory_path, report_path)
    (output / 'inputs-before.json').write_text(json.dumps(before, indent=2) + '\n')
    with (output / 'build.log').open('w') as log:
        subprocess.run(['lake', 'build', *groups], cwd=lean, stdout=log, stderr=subprocess.STDOUT, check=True)
    for index, (module, names) in enumerate(groups.items()):
        source = output / f'Audit{index}.lean'
        source.write_text(audit_source(module, names))
        logpath = output / f'audit{index}.log'
        with logpath.open('w') as log:
            subprocess.run(['lake', 'env', 'lean', str(source)], cwd=lean,
                           stdout=log, stderr=subprocess.STDOUT, check=True)
        observed = re.findall(r'^AUDIT OK: (\S+)$', logpath.read_text(), re.M)
        if observed != names:
            raise ValueError(f'audit output mismatch in {module}')
    after = fingerprints(project, lean, inventory_path, report_path)
    (output / 'inputs-after.json').write_text(json.dumps(after, indent=2) + '\n')
    if before != after:
        raise ValueError('proof inputs changed during audit')
    result = {'status': 'passed', 'scope': 'named Lean theorem and transitive axiom audit only',
              'checked': checked, 'mapping_metadata_checked': report is not None,
              'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
              'files_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in sorted(output.iterdir()) if p.is_file()}}
    (output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'Audited {len(checked)} theorems: {output}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('project', type=Path)
    parser.add_argument('--inventory', type=Path, required=True)
    parser.add_argument('--lean-dir', default='proofs')
    parser.add_argument('--proofs-toml', type=Path)
    parser.add_argument('--output', type=Path, required=True, help='New directory outside Lean sources')
    args = parser.parse_args()
    audit(args.project, args.inventory, args.lean_dir, args.output, args.proofs_toml)


if __name__ == '__main__':
    main()
