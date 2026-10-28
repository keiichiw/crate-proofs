#!/usr/bin/env python3
import os,subprocess
from pathlib import Path
r=Path(__file__).resolve().parents[1];env=dict(os.environ,INTEGER_NATIVE_LOG_DIR=str(Path(os.environ['AENEAS_RUN_DIR'])/'native'))
subprocess.run(['bash',str(r/'scripts/native-check.sh')],env=env,check=True)
