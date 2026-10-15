#!/usr/bin/env bash
set -euo pipefail

source /workspace/proof-env/scripts/activate.sh

REPO_ROOT=/workspace/proof-env
VERSION_DIR="$REPO_ROOT/percent-encoding/2.3.2"
CRATE_DIR="$VERSION_DIR/crate"
PROBE_DIR="$VERSION_DIR/verification/probes/utf8-model-module"
CHECKER="$PROBE_DIR/scripts/check_roots.py"
OUT_NAME="${1:?provide a fresh diagnostics subdirectory name}"
OUT_DIR="$PROBE_DIR/diagnostics/$OUT_NAME"
mkdir -p "$OUT_DIR"
exec > >(tee "$OUT_DIR/run.log") 2>&1

make_fingerprint() {
    find "$CRATE_DIR/src" "$CRATE_DIR/Cargo.toml" "$CRATE_DIR/Cargo.lock" \
        "$REPO_ROOT/form_urlencoded/1.2.2/crate/src/stdlib_models.rs" \
        "$REPO_ROOT/form_urlencoded/1.2.2/crate/Cargo.toml" \
        "$PROBE_DIR/scripts/run-error-model-checks.sh" "$CHECKER" \
        -type f -print0 | sort -z | xargs -0 sha256sum \
        | sed "s#  $REPO_ROOT/#  #"
}

{
    printf 'BEFORE\n'
    make_fingerprint
} > "$OUT_DIR/input-fingerprint.txt"
{
    cargo creusot --version
    rustc --version
    z3 --version
    cargo creusot --only=coma --span-mode off --output-dir "$OUT_DIR/coma" \
        -- --locked --offline --features alloc
} > "$OUT_DIR/translation-and-tools.log" 2>&1

export PROBE_Z3_TIMEOUT=5
COMA="$OUT_DIR/coma/verif/percent_encoding_rlib/utf8_models"
while IFS= read -r file; do
    name="$(basename "$file" .coma)"
    python3 "$CHECKER" "$file" "$OUT_DIR/direct-checks/$name"
done < <(find "$COMA" -maxdepth 1 -type f \
    \( -name 'utf8_step_bounds.coma' -o -name 'strict_error_*.coma' \) | sort)

python3 "$CHECKER" "$COMA/decode_utf8.coma" "$OUT_DIR/direct-checks/strict-helper"
python3 "$CHECKER" "$COMA/decode_utf8_lossy.coma" "$OUT_DIR/direct-checks/lossy-helper"
LIB_COMA="$OUT_DIR/coma/verif/percent_encoding_rlib/impl_PercentDecode_2"
python3 "$CHECKER" "$LIB_COMA/decode_utf8.coma" "$OUT_DIR/direct-checks/strict-public-wrapper"
python3 "$CHECKER" "$LIB_COMA/decode_utf8_lossy.coma" "$OUT_DIR/direct-checks/lossy-public-wrapper"

{
    printf 'AFTER\n'
    make_fingerprint
} >> "$OUT_DIR/input-fingerprint.txt"
awk '/^BEFORE$/{section=1;next}/^AFTER$/{section=2;next}section==1{print > before}section==2{print > after}' \
    before="$OUT_DIR/.before" after="$OUT_DIR/.after" "$OUT_DIR/input-fingerprint.txt"
if ! cmp -s "$OUT_DIR/.before" "$OUT_DIR/.after"; then
    printf 'Input source changed during the run.\n' >&2
    exit 1
fi
rm -f "$OUT_DIR/.before" "$OUT_DIR/.after"
