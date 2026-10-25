#!/usr/bin/env python3
"""Reject compiler/model patches or selection of the historical proof package."""
import json
import os
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[1]
profile = root / 'aeneas/profiles/unpatched'
sys.path.insert(0, str(root.parents[1] / 'scripts'))
from aeneas_management import tools

lock, key = tools.identity(profile)
for name in ('aeneas', 'charon'):
    spec = lock['repositories'][name]
    if spec.get('patches'):
        raise ValueError(f'{name} must have no patches in the unpatched profile')
store = root.parents[1] / '.work/tools' / key
tools.check(store, lock)
if Path(os.environ['AENEAS_SOURCE']).resolve() != (store / 'aeneas').resolve():
    raise ValueError('Wrong Aeneas source selected')
if Path(os.environ['AENEAS_LEAN_BACKEND']).resolve() != (store / 'aeneas/backends/lean').resolve():
    raise ValueError('Wrong Lean backend selected')
expected = root / '.work/build/unpatched' / tools.host() / 'proofs'
if Path(os.environ['AENEAS_PROOF_DIR']).resolve() != expected.resolve():
    raise ValueError('Historical proof package selected')
print('Unpatched compiler/backend sources and current proof package checked')
