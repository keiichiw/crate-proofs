#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/env.sh"
cd "$ADLER_ROOT"
git -C "$ADLER_ROOT/../.." submodule update --init --recursive -- adler2/2.0.1/upstream
python3 scripts/check-source.py
AENEAS_REV=be86ab0f1989d04944292b345b24c435be3ad10a
PROOFS_REV=2f439b8b37dac42e41f8b9dd805ba770d65fc239
SWITCH="${AENEAS_OPAM_SWITCH:-default}"
command -v opam
command -v gmake
command -v elan
rustup toolchain install 1.91.1 --profile minimal
mkdir -p .tools
checkout() {
  local url="$1" dir="$2" rev="$3"
  if [[ ! -d "$dir/.git" ]]; then git clone "$url" "$dir"; fi
  if [[ "$(git -C "$dir" rev-parse HEAD)" != "$rev" ]]; then
    test -z "$(git -C "$dir" status --porcelain)"
    git -C "$dir" fetch origin "$rev"
    git -C "$dir" checkout --detach "$rev"
  fi
}
checkout https://github.com/proofs-rs/proofs-rs.git .tools/proofs-rs "$PROOFS_REV"
checkout https://github.com/AeneasVerif/aeneas.git .tools/aeneas "$AENEAS_REV"
patch="$ADLER_ROOT/verification/patches/proofs-rs-audit-identifier.patch"
if ! git -C .tools/proofs-rs apply --reverse --check "$patch" 2>/dev/null; then
  git -C .tools/proofs-rs apply --check "$patch"
  git -C .tools/proofs-rs apply "$patch"
fi
cargo install --path .tools/proofs-rs/cli --locked --root .tools/cargo-proofs --force
elan toolchain install leanprover/lean4:v4.35.0
opam install --switch="$SWITCH" .tools/aeneas/src --deps-only -y
CHARON_REV="$(tail -1 .tools/aeneas/charon-pin)"
checkout https://github.com/AeneasVerif/charon.git .tools/aeneas/charon "$CHARON_REV"
git -C .tools/aeneas/charon submodule update --init --recursive
rustup toolchain install nightly-2026-09-17 --profile minimal --component rustc-dev,llvm-tools,rust-src
(cd .tools/aeneas/charon && env -u RUSTUP_TOOLCHAIN gmake build-dev-charon-rust charon-ml/src/CharonVersion.ml)
(cd .tools/aeneas && opam exec --switch="$SWITCH" -- gmake)
(cd proofs && lake update && lake exe cache get && lake build Aeneas)
bash scripts/verify.sh
