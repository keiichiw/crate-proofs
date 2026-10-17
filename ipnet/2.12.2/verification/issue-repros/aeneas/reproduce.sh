#!/usr/bin/env bash
set -euo pipefail

REPRO_ROOT="$(cd "$(dirname "$0")" && pwd)"
VERSION_ROOT="$(cd "$REPRO_ROOT/../../.." && pwd)"
source "$VERSION_ROOT/scripts/env.sh"
python3 "$VERSION_ROOT/scripts/check-tools.py"

mkdir -p "$REPRO_ROOT/runs"
RUN="$(mktemp -d "$REPRO_ROOT/runs/check-XXXXXXXX")"
export CARGO_TARGET_DIR="$RUN/target"
cargo +1.91.1 check --offline --locked --manifest-path "$REPRO_ROOT/Cargo.toml"

probe() {
  local name="$1"
  local out="$RUN/$name"
  mkdir -p "$out"
  (cd "$REPRO_ROOT" && charon cargo --preset=aeneas \
    --start-from "crate::$name" --dest-file "$out/repro.llbc" \
    -- --lib --locked) > "$out/charon.log" 2>&1
  if (cd "$REPRO_ROOT" && aeneas -backend lean -dest "$out" \
    "$out/repro.llbc") > "$out/aeneas.log" 2>&1; then
    echo 0 > "$out/aeneas.exit"
  else
    echo 1 > "$out/aeneas.exit"
  fi
}

probe mutable_dyn_write
grep -q 'Unsupported cast to a dynamic trait' "$RUN/mutable_dyn_write/aeneas.log"
test "$(cat "$RUN/mutable_dyn_write/aeneas.exit")" = 1

probe next_ascii
test "$(cat "$RUN/next_ascii/aeneas.exit")" = 0
if (cd "$VERSION_ROOT/proofs" && lake env lean \
  "$RUN/next_ascii/Repro.lean") > "$RUN/next_ascii/lean.log" 2>&1; then
  echo 'Expected the borrowed FnOnce generated Lean to fail' >&2
  exit 1
fi
grep -q 'expected a product type, got' "$RUN/next_ascii/lean.log"
grep -q 'Result (Option U8 × Cursor)' "$RUN/next_ascii/lean.log"

probe extend_bytes
test "$(cat "$RUN/extend_bytes/aeneas.exit")" = 1
grep -q 'Internal error' "$RUN/extend_bytes/aeneas.log"

python3 "$REPRO_ROOT/package-evidence.py" "$RUN"
echo "Pinned Aeneas reproductions matched; logs: $RUN"
