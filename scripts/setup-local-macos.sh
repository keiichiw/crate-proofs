#!/usr/bin/env bash
# Install the pinned tools without replacing the existing user Creusot/Opam switch.
set -euo pipefail
repo_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
[[ $(uname -s) == Darwin && $(uname -m) == arm64 ]] || {
  echo 'This bootstrap supports macOS arm64; use setup-cloud.sh for the recorded Linux environment.' >&2
  exit 1
}
(( BASH_VERSINFO[0] >= 4 )) || { echo "Bash 4 or newer is required; install a current Bash and invoke this script with it." >&2; exit 1; }
for tool in git curl rustup cargo opam python3 unzip make cc pkg-config autoconf automake; do
  command -v "$tool" >/dev/null || { echo "Missing prerequisite: $tool" >&2; exit 1; }
done
source "$repo_dir/scripts/activate-local.sh"
mkdir -p "$PROOF_LOCAL_ROOT/sources" "$PROOF_LOCAL_ROOT/logs" "$CREUSOT_DATA_HOME/bin"
rustup set auto-self-update disable
rustup toolchain install 1.91.0 --profile minimal --component rust-src
rustup default 1.91.0
rustup toolchain install nightly-2026-06-22 --profile minimal --component rustc-dev --component llvm-tools --component rustfmt --component rust-src

checkout_pin() {
  local name=$1 url=$2 revision=$3
  local path="$PROOF_LOCAL_ROOT/sources/$name"
  if [[ ! -d "$path/.git" ]]; then
    git init "$path"
    git -C "$path" remote add origin "$url"
  fi
  if ! git -C "$path" cat-file -e "$revision^{commit}" 2>/dev/null; then
    git -C "$path" fetch --depth 1 origin "$revision"
  fi
  [[ -z $(git -C "$path" status --porcelain) ]] || { echo "Modified tool source: $path" >&2; exit 1; }
  git -C "$path" checkout --detach "$revision"
  [[ $(git -C "$path" rev-parse HEAD) == "$revision" ]]
}
checkout_pin creusot https://github.com/creusot-rs/creusot.git 318615be3b8bbc60d1f6d52469ba5c0bdebed4f1
checkout_pin proofs-rs https://github.com/proofs-rs/proofs-rs.git f6797340912a6231e55668a31b8b36746d4bc65c
cd "$PROOF_LOCAL_ROOT/sources/creusot"
cargo +nightly-2026-06-22 install --locked --path cargo-creusot
cargo +nightly-2026-06-22 install --locked --path creusot-rustc --root "$CREUSOT_DATA_HOME/toolchains/nightly-2026-06-22"
# Do not invoke the installer's macOS Why3 step: it uses the user's ~/.creusot switch.
# Do not invoke why3-conf: it can write into the existing user's macOS config directory.
cargo +nightly-2026-06-22 run --locked --bin creusot-install -- prelude provers
cp why3find.json "$CREUSOT_DATA_HOME/why3find.json"
cp creusot-install/creusot_why3.conf "$CREUSOT_DATA_HOME/creusot_why3.conf"

if [[ ! -f "$OPAMROOT/config" ]]; then
  opam init --bare --no-setup -y --disable-sandboxing default https://github.com/ocaml/opam-repository.git
fi
opam --cli=2.1 var --global in-creusot-ci=true
if [[ ! -d "$CREUSOT_DATA_HOME/_opam/.opam-switch" ]]; then
  opam switch create -y --empty "$CREUSOT_DATA_HOME"
fi
opam install -y --switch="$CREUSOT_DATA_HOME" ocaml-base-compiler.5.3.0
why3_archive="$PROOF_LOCAL_ROOT/sources/why3-source.tar.gz"
if [[ ! -f "$why3_archive" ]]; then
  curl --fail --location --retry 3 --max-time 600 \
    https://gitlab.inria.fr/why3/why3/-/archive/54c92f96bb0711d6e991c18f10bfbc08d90d028b/why3-54c92f96bb0711d6e991c18f10bfbc08d90d028b.tar.gz \
    -o "$why3_archive"
fi
printf '%s  %s\n' c4b57a5904ac4f52b815028cbade036540270a82f75e12a1cae3d49a4f8d5a81 "$why3_archive" | shasum -a 256 -c -
why3_source="$PROOF_LOCAL_ROOT/sources/why3"
mkdir -p "$why3_source"
tar -xzf "$why3_archive" --strip-components=1 -C "$why3_source"
mkdir -p "$why3_source/opam"
for package in why3 why3-ide; do
  curl --fail --location --retry 3 --max-time 60 \
    "https://gitlab.inria.fr/api/v4/projects/why3%2Fwhy3/repository/files/opam%2F${package}.opam/raw?ref=54c92f96bb0711d6e991c18f10bfbc08d90d028b" \
    -o "$why3_source/opam/$package.opam"
done
[[ $(git hash-object "$why3_source/opam/why3.opam") == d6262582d6375722a0b7552c89928749bdfd012d ]]
[[ $(git hash-object "$why3_source/opam/why3-ide.opam") == 6c87545bd1dc603a08d3202a25b4ae6e5b06dcfd ]]
opam pin add --no-action -y --switch="$CREUSOT_DATA_HOME" why3.git-54c92f96 "$why3_source"
opam pin add --no-action -y --switch="$CREUSOT_DATA_HOME" why3find.git-eab37557 'git+https://github.com/creusot-rs/why3find.git#eab37557d3e24e1913a3c4f44bc5528ef497c6c9'
OPAMIGNOREPINDEPENDS=true opam install -y --switch="$CREUSOT_DATA_HOME" why3.git-54c92f96 why3find.git-eab37557 ocamlgraph camlzip zarith
ln -sfn "$CREUSOT_DATA_HOME/_opam/bin/why3" "$CREUSOT_DATA_HOME/bin/why3"
ln -sfn "$CREUSOT_DATA_HOME/_opam/bin/why3find" "$CREUSOT_DATA_HOME/bin/why3find"
cargo +1.91.0 install --locked --path "$PROOF_LOCAL_ROOT/sources/proofs-rs/cli"
bash "$repo_dir/scripts/check-local-tools.sh"
