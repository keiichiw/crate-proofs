#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/env.sh"
cd "$ADLER_ROOT"
python3 scripts/check-source.py
out="${1:?Usage: extract.sh OUTPUT_DIRECTORY}"
mkdir -p "$out"
out="$(cd "$out" && pwd)"
charon cargo --preset=aeneas \
  --start-from crate::Adler32::new \
  --start-from crate::Adler32::from_checksum \
  --start-from crate::Adler32::checksum \
  --start-from crate::Adler32::write_slice \
  --start-from crate::adler32_slice \
  --dest-file "$out/adler2.llbc" -- --lib --locked
aeneas -backend lean -dest "$out" "$out/adler2.llbc"
test -s "$out/Adler2.lean"
python3 - "$out/Adler2.lean" <<'PY'
from pathlib import Path
import re
import sys

path = Path(sys.argv[1])
source = path.read_text()
forbidden = re.search(r"(?m)^\s*(?:axiom|opaque|partial\s+def)\b|\bsorry\b", source)
if forbidden:
    raise SystemExit(f"generated model contains an unsupported declaration at byte {forbidden.start()}")
required = [
    "Adler32.new", "Adler32.from_checksum", "Adler32.checksum",
    "algo.U32X4.from", "algo.Adler32.compute", "Adler32.write_slice",
    "adler32_slice",
]
missing = [name for name in required if not re.search(rf"(?m)^def {re.escape(name)}\b", source)]
if missing:
    raise SystemExit(f"generated model lacks selected local definitions: {', '.join(missing)}")
if "adler2_1." in source:
    raise SystemExit("generated model unexpectedly includes the registry adler2 copy")
print("Generated local model inventory and absence of axioms/sorry: OK")
PY
