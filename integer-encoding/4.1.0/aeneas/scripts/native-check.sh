#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"

export RUSTUP_TOOLCHAIN=1.91.1
export CARGO_INCREMENTAL=0
LOG_DIR="${INTEGER_NATIVE_LOG_DIR:-$ROOT/.work/runs/native-logs}"
TARGET="$ROOT/.work/build/native-direct"
mkdir -p "$LOG_DIR" "$TARGET"
exec 3> "$LOG_DIR/commands.log"
export BASH_XTRACEFD=3
set -x
rustc --version > "$LOG_DIR/toolchain.log"
cargo metadata --locked --offline --format-version=1 --no-deps --manifest-path "$ROOT/Cargo.toml" > "$LOG_DIR/cargo-metadata.json"
python3 - "$ROOT" "$LOG_DIR" <<'PY'
from pathlib import Path
import hashlib,json,sys
r,d=map(Path,sys.argv[1:]);m=json.loads((d/'cargo-metadata.json').read_text());p=next(p for p in m['packages'] if p['name']=='integer-encoding');assert all(x['optional'] or x['kind']=='dev' for x in p['dependencies']);assert m['resolve'] is None;assert p['features'].get('default',[])==[]
(d/'native-inputs.json').write_text(json.dumps({'default_active_external_dependencies':0,'source':'unchanged upstream/src/lib.rs','feature_configuration':'default (no feature cfg flags)','host_pointer_bits':64,'sha256':{n:hashlib.sha256((r/n).read_bytes()).hexdigest() for n in ['Cargo.toml','Cargo.lock','tests/native.rs','tests/reproduce.rs','scripts/native-check.sh','scripts/native-results.py']+[str(f.relative_to(r)) for f in sorted((r/'upstream/src').glob('*.rs'))]}},indent=2)+'\n')
PY
for PROFILE in debug release; do
 FLAGS=(-C overflow-checks=yes -C debug-assertions=yes -C opt-level=0)
 if [[ "$PROFILE" == release ]]; then FLAGS=(-C overflow-checks=no -C debug-assertions=no -C opt-level=3); fi
 printf '%q ' rustc --edition=2018 --crate-name integer_encoding --crate-type rlib "$ROOT/upstream/src/lib.rs" "${FLAGS[@]}" -o "$TARGET/libinteger_encoding-$PROFILE.rlib" > "$LOG_DIR/commands-$PROFILE.log"
 printf '\n' >> "$LOG_DIR/commands-$PROFILE.log"
 rustc --edition=2018 --crate-name integer_encoding --crate-type rlib "$ROOT/upstream/src/lib.rs" "${FLAGS[@]}" -o "$TARGET/libinteger_encoding-$PROFILE.rlib" > "$LOG_DIR/compile-lib-$PROFILE.log" 2>&1
 rustc --edition=2021 --test "$ROOT/tests/native.rs" --extern "integer_encoding=$TARGET/libinteger_encoding-$PROFILE.rlib" "${FLAGS[@]}" -o "$TARGET/native-$PROFILE" > "$LOG_DIR/compile-tests-$PROFILE.log" 2>&1
 "$TARGET/native-$PROFILE" --list > "$LOG_DIR/native-list-$PROFILE.log"
 "$TARGET/native-$PROFILE" --test-threads=1 --nocapture > "$LOG_DIR/native-$PROFILE.log" 2>&1
 rustc --edition=2021 "$ROOT/tests/reproduce.rs" --extern "integer_encoding=$TARGET/libinteger_encoding-$PROFILE.rlib" "${FLAGS[@]}" -o "$TARGET/reproduce-$PROFILE" > "$LOG_DIR/compile-reproduce-$PROFILE.log" 2>&1
 "$TARGET/reproduce-$PROFILE" > "$LOG_DIR/reproduce-$PROFILE.log" 2>&1
 done
rustc --edition=2018 --test "$ROOT/upstream/src/lib.rs" -C overflow-checks=yes -C debug-assertions=yes -o "$TARGET/upstream-tests" > "$LOG_DIR/compile-upstream.log" 2>&1
"$TARGET/upstream-tests" --list > "$LOG_DIR/upstream-list.log"
"$TARGET/upstream-tests" --test-threads=1 --nocapture > "$LOG_DIR/upstream.log" 2>&1
rustdoc --edition=2018 --test "$ROOT/upstream/src/lib.rs" --extern "integer_encoding=$TARGET/libinteger_encoding-debug.rlib" > "$LOG_DIR/doc.log" 2>&1
set +x
exec 3>&-
python3 "$ROOT/scripts/native-results.py" "$LOG_DIR"
