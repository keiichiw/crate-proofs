#!/usr/bin/env bash
set -euo pipefail
version_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$version_dir"
if [[ $# -gt 1 ]]; then
  echo "usage: $0 [OUTPUT_DIRECTORY]" >&2
  exit 2
fi
if [[ $# -eq 1 ]]; then
  run_dir=$1
else
  mkdir -p "$version_dir/evidence"
  run_dir=$(mktemp -d "$version_dir/evidence/differential-XXXXXXXX")
fi
mkdir -p "$run_dir"
python3 - "$version_dir" <<'PY'
import hashlib
from pathlib import Path
import sys
version = Path(sys.argv[1])
source = version / "capture/source/src"
copy = version / "verification/differential/upstream-copy/src"
def hashes(root):
    return {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(root.rglob("*.rs"))}
if hashes(source) != hashes(copy):
    raise SystemExit("upstream-copy Rust source differs from immutable capture/source")
print("Upstream-copy Rust source hashes match immutable capture source.")
PY
CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$version_dir/target/differential}" \
  cargo run --locked --manifest-path verification/differential/Cargo.toml \
  2>&1 | tee "$run_dir/run.log"

cargo test --locked --all-features > "$run_dir/tests.log" 2>&1
cargo check --locked --no-default-features --features alloc > "$run_dir/check-alloc.log" 2>&1
printf 'Native results: %s\n' "$run_dir"
