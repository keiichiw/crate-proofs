#!/usr/bin/env python3
import json,os,subprocess
from pathlib import Path
r=Path(__file__).resolve().parents[1];p=r/'aeneas/profiles/default';run=Path(os.environ['AENEAS_RUN_DIR']);config=json.loads((p/'extraction.json').read_text())
actual=json.loads((run/'extraction-0'/config['llbc']).read_text())['translated']['runtime_checks']
if actual!=json.loads((p/'runtime-checks.json').read_text()):raise ValueError('Extraction runtime checks changed')
subprocess.run(['lake','env','lean',str(r/'tests/ShiftChecks.lean')],cwd=os.environ['AENEAS_PROOF_DIR'],check=True)
print('Exact LLBC runtime checks and checked shift overflow models: OK')
