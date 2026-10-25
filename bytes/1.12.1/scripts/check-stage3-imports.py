#!/usr/bin/env python3
"""Check the new header-import option rejects raw Lean source injection."""
import json
from pathlib import Path
import subprocess
import sys

binary = Path(sys.argv[1]).resolve()
out = Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=False)
cases = [('BytesStage3Types', True), ('Aeneas.Std.Slice', True),
         ('', False), ('.Bad', False), ('Bad.', False), ('A..B', False),
         ('1Bad', False), ('A; axiom bad : False', False),
         ('A\naxiom bad : False', False), ('../A', False)]
results = []
for i, (name, valid) in enumerate(cases):
    p = subprocess.run([str(binary), '-lean-import', name, '-help'],
                       capture_output=True, text=True)
    (out / f'{i}.stdout').write_text(p.stdout)
    (out / f'{i}.stderr').write_text(p.stderr)
    if valid:
        assert p.returncode == 0, (name, p.returncode)
    else:
        assert p.returncode != 0 and 'dotted Lean module identifier' in p.stderr, (name, p.returncode)
    results.append({'module': name, 'valid': valid, 'returncode': p.returncode})
(out / 'result.json').write_text(json.dumps(results, indent=2) + '\n')
print('Lean header import identifier guards: passed')
