#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../../.." && pwd)
cd "$REPO_ROOT"
DIFFERENTIAL_DIR="$REPO_ROOT/percent-encoding/2.3.2/verification/differential"
FORK_MANIFEST="$REPO_ROOT/percent-encoding/2.3.2/crate/Cargo.toml"
UPSTREAM_MANIFEST="$DIFFERENTIAL_DIR/upstream-copy/Cargo.toml"
RUN_ID="percent-encoding-2.3.2-full-scope-$(date -u +%Y%m%dT%H%M%SZ)-$$"
FINGERPRINT_FILE="$DIFFERENTIAL_DIR/source-fingerprint-full-scope.txt"

make_fingerprint() {
    local inputs=(
        "$REPO_ROOT/percent-encoding/2.3.2/crate/src"
        "$REPO_ROOT/percent-encoding/2.3.2/crate/Cargo.toml" \
        "$REPO_ROOT/percent-encoding/2.3.2/crate/Cargo.lock" \
        "$REPO_ROOT/percent-encoding/2.3.2/capture/source" \
        "$DIFFERENTIAL_DIR/Cargo.toml" "$DIFFERENTIAL_DIR/Cargo.lock" \
        "$DIFFERENTIAL_DIR/src" "$DIFFERENTIAL_DIR/run-full-scope.sh" \
        "$DIFFERENTIAL_DIR/upstream-copy/Cargo.toml" \
        "$DIFFERENTIAL_DIR/upstream-copy/Cargo.lock" \
        "$DIFFERENTIAL_DIR/upstream-copy/src"
    )
    for optional in \
        "$REPO_ROOT/percent-encoding/2.3.2/crate/.cargo/config.toml" \
        "$DIFFERENTIAL_DIR/.cargo/config.toml"; do
        if [[ -f "$optional" ]]; then
            inputs+=("$optional")
        fi
    done
    python3 - "$REPO_ROOT" "${inputs[@]}" <<'PYHASH'
import hashlib, sys
from pathlib import Path
root = Path(sys.argv[1])
files = set()
for item in sys.argv[2:]:
    path = Path(item)
    files.update(p for p in path.rglob("*") if p.is_file()) if path.is_dir() else files.add(path)
for path in sorted(files):
    print(f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.relative_to(root)}")
PYHASH
}

{
    printf 'RUN_ID=%s\nBEFORE\n' "$RUN_ID"
    make_fingerprint
} > "$FINGERPRINT_FILE"

run_logged() {
    local log_name="$1"
    shift
    {
        printf 'RUN_ID=%s\n' "$RUN_ID"
        "$@"
    } > "$DIFFERENTIAL_DIR/$log_name" 2>&1
}

run_logged differential-run-full-scope.log \
    env PERCENT_ENCODING_RUN_ID="$RUN_ID" \
    CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$DIFFERENTIAL_DIR/target-full-scope}" cargo run --locked \
    --manifest-path "$DIFFERENTIAL_DIR/Cargo.toml" --release

run_logged fork-unit-all-features-full-scope.log \
    env CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$DIFFERENTIAL_DIR/target-fork-full-scope}" cargo test --locked --all-features \
    --manifest-path "$FORK_MANIFEST"
run_logged fork-doc-all-features-full-scope.log \
    env CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$DIFFERENTIAL_DIR/target-fork-full-scope}" cargo test --locked --doc --all-features \
    --manifest-path "$FORK_MANIFEST"
run_logged fork-check-default-full-scope.log \
    env CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$DIFFERENTIAL_DIR/target-fork-full-scope}" cargo check --locked \
    --manifest-path "$FORK_MANIFEST"
run_logged fork-check-bare-full-scope.log \
    env CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$DIFFERENTIAL_DIR/target-fork-full-scope}" cargo check --locked --no-default-features \
    --manifest-path "$FORK_MANIFEST"
run_logged fork-check-alloc-full-scope.log \
    env CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$DIFFERENTIAL_DIR/target-fork-full-scope}" cargo check --locked --no-default-features --features alloc \
    --manifest-path "$FORK_MANIFEST"
run_logged upstream-unit-all-features-full-scope.log \
    env CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$DIFFERENTIAL_DIR/target-upstream-full-scope}" cargo test --locked --all-features \
    --manifest-path "$UPSTREAM_MANIFEST"

{
    printf 'AFTER\n'
    make_fingerprint
} >> "$FINGERPRINT_FILE"

BEFORE_FILE="$DIFFERENTIAL_DIR/.fingerprint-before.tmp"
AFTER_FILE="$DIFFERENTIAL_DIR/.fingerprint-after.tmp"
sed -n '/^BEFORE$/,/^AFTER$/{ /^BEFORE$/d; /^AFTER$/d; p; }' "$FINGERPRINT_FILE" > "$BEFORE_FILE"
sed -n '/^AFTER$/,$p' "$FINGERPRINT_FILE" | sed '1d' > "$AFTER_FILE"
if ! cmp -s "$BEFORE_FILE" "$AFTER_FILE"; then
    rm -f "$BEFORE_FILE" "$AFTER_FILE"
    printf 'Source/config fingerprint changed during the native run.\n' >&2
    exit 1
fi
rm -f "$BEFORE_FILE" "$AFTER_FILE"
printf 'Native run %s passed; logs: %s\n' "$RUN_ID" "$DIFFERENTIAL_DIR"
