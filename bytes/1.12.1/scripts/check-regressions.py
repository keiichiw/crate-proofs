#!/usr/bin/env python3
"""Mandatory compiler failure controls and finite native signed-read observation."""
import os,subprocess,sys
from pathlib import Path
r=Path(__file__).resolve().parents[1];p=r/'aeneas/profiles/default';run=Path(os.environ['AENEAS_RUN_DIR'])
core=Path(os.environ['AENEAS_SOURCE'])/'bin/aeneas';numeric=os.environ['AENEAS_NUMERIC_BIN'];stage3=os.environ['AENEAS_STAGE3_BIN']
commands=[
 [p/'blockers/shared-reborrow-stage2/reproduce.py',numeric,run/'numeric-reborrow-regression','--combined-reviewed-tool'],
 [p/'blockers/declaration-order-stage2/reproduce.py',numeric,run/'numeric-order-regression'],
 [r/'scripts/check-rooted-repair.py',core,run/'rooted-regression','--llbc',run/'adapters-generated/bytes_adapters.llbc'],
 [r/'scripts/check-stage3-imports.py',stage3,run/'import-guards'],
 [r/'scripts/check-branch-joins.py',core,stage3,run/'branch-join-regression'],
 [r/'scripts/check-never-repair.py',core,run/'never-regression']]
for args in commands:subprocess.run([sys.executable,*map(str,args)],cwd=r,check=True)
actual=subprocess.check_output(['cargo','run','--offline','--quiet','--locked','--manifest-path',str(p/'findings/signed-read/Cargo.toml')],cwd=r)
(run/'signed-read-observed.txt').write_bytes(actual)
if actual!=(p/'findings/signed-read/observed.txt').read_bytes():raise ValueError('Signed-read observation differs')
print('Compiler repair controls and signed-read observation reproduced; not application proof claims')
