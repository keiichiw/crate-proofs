#!/usr/bin/env python3
"""Directly check every generated goal for the DebugStruct trace adapters."""
from __future__ import annotations
import json
from pathlib import Path
import subprocess
import sys

base = Path(sys.argv[1]).resolve()
out = Path(sys.argv[2]).resolve()
selected = {
    "trace/impl_DebugTrace/empty": base / "debug_trace/impl_DebugTrace/empty.coma",
    "ascii_set/Debug::fmt": base / "ascii_set/impl_Debug_for_AsciiSet/fmt.coma",
    "trace/start": base / "debug_trace/start.coma",
    "trace/field_words": base / "debug_trace/field_words.coma",
    "trace/field_bytes": base / "debug_trace/field_bytes.coma",
    "trace/field_byte_iter": base / "debug_trace/field_byte_iter.coma",
    "trace/field_ascii_set": base / "debug_trace/field_ascii_set.coma",
    "trace/finish": base / "debug_trace/finish.coma",
    "probe/trace_mask": base / "trace_mask.coma",
    "probe/trace_encoder": base / "trace_encoder.coma",
    "probe/trace_decoder": base / "trace_decoder.coma",
}
checker = Path(__file__).with_name("check_roots.py")
reports = {}
for index, (name, coma) in enumerate(selected.items()):
    target = out / f"{index:02d}-{name.replace('/', '-') }"
    result = subprocess.run(
        [sys.executable, str(checker), str(coma), str(target)],
        cwd=Path.cwd(),
        text=True,
        capture_output=True,
        check=False,
    )
    reports[name] = {"exit_code": result.returncode, "stdout": result.stdout, "stderr": result.stderr}
    if result.returncode:
        print(json.dumps({"status": "failed", "target": name, "reports": reports}))
        raise SystemExit(1)
print(json.dumps({"status": "passed", "target_count": len(reports), "reports": reports}))
