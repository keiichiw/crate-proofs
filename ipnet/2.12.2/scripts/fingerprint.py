#!/usr/bin/env python3
import hashlib
import json
import subprocess
from pathlib import Path
root = Path(__file__).resolve().parents[1]
paths = ['Cargo.toml', 'Cargo.lock', 'rust-toolchain.toml', 'proofs.toml', 'AGENTS.md', 'README.md',
         'upstream/src', 'upstream/Cargo.toml', 'upstream/Cargo.lock', 'verification/upstream.json', 'tests', 'scripts', 'proofs', 'capture', 'verification/plan.md', 'verification/aeneas.json',
         'verification/toolchain.json', 'verification/specification.md', 'verification/set-operations-specification.md', 'verification/expert-review.txt', 'verification/expert-contains-review.txt', 'verification/contains-specification.md', 'verification/range-next-specification.md', 'verification/ipv4-api-specification.md', 'verification/ipv4-tagged-value-specification.md', 'verification/ipv6-tagged-value-specification.md', 'verification/ipv6-coverage.md', 'verification/ipv6-iteration-specification.md', 'verification/remaining-tagged-specification.md', 'verification/ipv4-subnets-specification.md', 'verification/ipv4-coverage.md', 'verification/ipv4-remaining-coverage.md', 'verification/ipv4-aggregate-boundaries.md', 'verification/blockers/aggregate-extend/README.md', 'verification/blockers/aggregate-extend/evidence.json', 'verification/blockers/ipv4-parser-callback/README.md', 'verification/blockers/ipv4-parser-callback/evidence.json', 'verification/model-boundaries.md', 'verification/std-source-boundaries.json', 'verification/extraction-notes.md', 'verification/theorems.json', 'verification/patches', 'verification/opam-switch.export', '.tools/cargo-proofs/bin/cargo-proofs',
         '.tools/aeneas/bin/aeneas', '.tools/aeneas/charon/bin/charon',
         '.tools/aeneas/charon/bin/charon-driver']
files = []
for name in paths:
    p = root / name
    files.extend(p.rglob('*') if p.is_dir() else [p])
fingerprints = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in sorted(files) if p.is_file() and '.lake' not in p.parts and '__pycache__' not in p.parts}
repo = Path(subprocess.check_output(['git','-C',str(root),'rev-parse','--show-toplevel'],text=True).strip())
fingerprints['@superproject/.gitmodules'] = hashlib.sha256((repo/'.gitmodules').read_bytes()).hexdigest()
fingerprints['@upstream/HEAD'] = subprocess.check_output(['git','-C',str(root/'upstream'),'rev-parse','HEAD'],text=True).strip()
for name in ['scripts/aeneas-extract.py', 'scripts/aeneas-audit.py']:
    fingerprints['@shared/' + name] = hashlib.sha256((repo/name).read_bytes()).hexdigest()
print(json.dumps(fingerprints, indent=2))
