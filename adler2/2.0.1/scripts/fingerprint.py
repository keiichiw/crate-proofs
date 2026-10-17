#!/usr/bin/env python3
import hashlib
import json
import subprocess
from pathlib import Path
root = Path(__file__).resolve().parents[1]
paths = ['Cargo.toml', 'Cargo.lock', 'rust-toolchain.toml', 'proofs.toml', 'AGENTS.md', 'README.md',
         'upstream/src', 'upstream/Cargo.toml', 'verification/upstream.json', 'tests', 'scripts', 'proofs', 'capture', 'verification/plan.md',
         'verification/toolchain.json', 'verification/specification.md', 'verification/theorems.json', 'verification/patches', 'verification/opam-switch.export', '.tools/cargo-proofs/bin/cargo-proofs',
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
print(json.dumps(fingerprints, indent=2))
