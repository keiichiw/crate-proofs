#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/env.sh"
cd "$IPNET_ROOT"
git -C "$IPNET_ROOT/../.." submodule update --init --recursive -- ipnet/2.12.2/upstream
python3 scripts/check-source.py
AENEAS_REV=8e62dc3dc765602833c86b68dceb18a475a50a8f
PROOFS_REV=a2335432635301597f203e1159e3d16888ce2333
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
aeneas_patch="$IPNET_ROOT/verification/patches/aeneas-runtime-ipv6-constructor.patch"
if ! git -C .tools/aeneas apply --reverse --check "$aeneas_patch" 2>/dev/null; then
  git -C .tools/aeneas apply --check "$aeneas_patch"
  git -C .tools/aeneas apply --intent-to-add "$aeneas_patch"
fi
patch="$IPNET_ROOT/verification/patches/proofs-rs-audit-identifier.patch"
if ! git -C .tools/proofs-rs apply --reverse --check "$patch" 2>/dev/null; then
  git -C .tools/proofs-rs apply --check "$patch"
  git -C .tools/proofs-rs apply "$patch"
fi
cargo install --path .tools/proofs-rs/cli --locked --root .tools/cargo-proofs --force
elan toolchain install leanprover/lean4:v4.35.0
opam install --switch="$SWITCH" .tools/aeneas/src --deps-only -y
CHARON_REV="$(tail -1 .tools/aeneas/charon-pin)"
checkout https://github.com/AeneasVerif/charon.git .tools/aeneas/charon "$CHARON_REV"
charon_patch="$IPNET_ROOT/verification/patches/charon-runtime-ipv6-matcher.patch"
if ! git -C .tools/aeneas/charon apply --reverse --check "$charon_patch" 2>/dev/null; then
  git -C .tools/aeneas/charon apply --check "$charon_patch"
  git -C .tools/aeneas/charon apply "$charon_patch"
fi
git -C .tools/aeneas/charon submodule update --init --recursive
rustup toolchain install nightly-2026-09-17 --profile minimal --component rustc-dev,llvm-tools,rust-src
(cd .tools/aeneas/charon && env -u RUSTUP_TOOLCHAIN gmake build-dev-charon-rust charon-ml/src/CharonVersion.ml)
# Regenerate model registration metadata, including unused unwrap dictionary erasure.
(cd .tools/aeneas/backends/lean && lake exe cache get && lake build Aeneas && lake exe extract)
(cd .tools/aeneas && opam exec --switch="$SWITCH" -- gmake)
# Install exactly the lockfile's Aeneas source, applying the same backend patch.
# This also works when the package is a local symlink to the dedicated tool checkout.
mkdir -p proofs/.lake/packages
checkout https://github.com/AeneasVerif/aeneas proofs/.lake/packages/aeneas "$AENEAS_REV"
if ! git -C proofs/.lake/packages/aeneas apply --reverse --check "$aeneas_patch" 2>/dev/null; then
  git -C proofs/.lake/packages/aeneas apply --check "$aeneas_patch"
  git -C proofs/.lake/packages/aeneas apply --intent-to-add "$aeneas_patch"
fi
(cd proofs && test -f lake-manifest.json && lake exe cache get && lake build Aeneas)
bash scripts/verify.sh
