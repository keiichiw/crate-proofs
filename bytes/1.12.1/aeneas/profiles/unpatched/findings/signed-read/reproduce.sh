#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/../../../../.." && pwd)
source "$root/scripts/env.sh"
CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$root/.work/build/signed-read-target} \
  cargo run --offline --quiet --locked --manifest-path "$root/aeneas/profiles/unpatched/findings/signed-read/Cargo.toml"
