#!/usr/bin/env bash
set -euo pipefail
# Run from the existing isolated cloud checkout; do not create a worktree.
mkdir -p /workspace/.setup /workspace/.local /workspace/.setup/debs
export CARGO_HOME=/workspace/.cargo RUSTUP_HOME=/workspace/.rustup
export PATH=/workspace/.cargo/bin:$PATH
if ! command -v rustup >/dev/null; then
  curl --fail --location https://sh.rustup.rs -o /workspace/.setup/rustup-init.sh
  sh /workspace/.setup/rustup-init.sh -y --no-modify-path --profile minimal --default-toolchain 1.91.0
fi
if ! rustup toolchain list | rg -q '^1\.91\.0-x86_64-unknown-linux-gnu'; then
  rustup toolchain install 1.91.0 --profile minimal
fi
if ! rustup toolchain list | rg -q '^nightly-2026-06-22-x86_64-unknown-linux-gnu'; then
  rustup toolchain install nightly-2026-06-22 --profile minimal --component rustc-dev --component llvm-tools --component rustfmt
else
  for component in rustc-dev llvm-tools rustfmt; do
    if ! rustup component list --toolchain nightly-2026-06-22 --installed | rg -qx "${component}-x86_64-unknown-linux-gnu"; then
      rustup component add --toolchain nightly-2026-06-22 "$component"
    fi
  done
fi
mkdir -p /workspace/.setup/apt/lists/partial /workspace/.setup/apt/archives/partial /workspace/.setup/apt/empty
cat > /workspace/.setup/apt/sources.list <<'EOF'
deb [signed-by=/usr/share/keyrings/debian-archive-keyring.gpg] https://deb.debian.org/debian trixie main
EOF
cat > /workspace/.setup/apt/apt.conf <<'EOF'
Dir::Etc::main "-";
Dir::Etc::parts "/workspace/.setup/apt/empty";
Dir::Etc::sourcelist "/workspace/.setup/apt/sources.list";
Dir::Etc::sourceparts "/workspace/.setup/apt/empty";
Dir::State::lists "/workspace/.setup/apt/lists";
Dir::Cache::archives "/workspace/.setup/apt/archives";
APT::Sandbox::User "agent";
EOF
export APT_CONFIG=/workspace/.setup/apt/apt.conf
/usr/bin/apt-get update
cd /workspace/.setup/debs
/usr/bin/apt-get download opam opam-installer libglpk40 libamd3 libcolamd3 libsuitesparseconfig7 libltdl7 libgmp-dev libzmq3-dev libzmq5 libsodium-dev libpgm-dev libnorm-dev libbsd-dev libmd-dev libxml2-dev rsync libpopt0 autoconf m4
for archive in *.deb; do dpkg-deb -x "$archive" /workspace/.local; done
cat > /workspace/.setup/activate.sh <<'ACTIVATE'
export CARGO_HOME=/workspace/.cargo
export RUSTUP_HOME=/workspace/.rustup
export OPAMROOT=/workspace/.opam
export XDG_DATA_HOME=/workspace/.local/share
export XDG_CONFIG_HOME=/workspace/.config
export XDG_CACHE_HOME=/workspace/.cache
export PATH=/workspace/.cargo/bin:/workspace/.local/usr/bin:/workspace/.local/share/creusot/bin:$PATH
export LD_LIBRARY_PATH=/workspace/.local/usr/lib/x86_64-linux-gnu${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}
export CARGO_BUILD_JOBS=4
export OPAMJOBS=4
export PKG_CONFIG_PATH=/workspace/.local/usr/lib/x86_64-linux-gnu/pkgconfig${PKG_CONFIG_PATH:+:$PKG_CONFIG_PATH}
export PKG_CONFIG_SYSROOT_DIR=/workspace/.local
export C_INCLUDE_PATH=/workspace/.local/usr/include:/workspace/.local/usr/include/x86_64-linux-gnu${C_INCLUDE_PATH:+:$C_INCLUDE_PATH}
export LIBRARY_PATH=/workspace/.local/usr/lib/x86_64-linux-gnu${LIBRARY_PATH:+:$LIBRARY_PATH}
export autom4te_perllibdir=/workspace/.local/usr/share/autoconf
export AC_MACRODIR=/workspace/.local/usr/share/autoconf
export AUTOM4TE=/workspace/.local/usr/bin/autom4te
export M4=/workspace/.local/usr/bin/m4
export AUTOM4TE='/workspace/.local/usr/bin/autom4te --prepend-include=/workspace/.local/usr/share/autoconf'
export trailer_m4=/workspace/.local/usr/share/autoconf/autoconf/trailer.m4
ACTIVATE
source /workspace/.setup/activate.sh
test "$(git -C /workspace/creusot rev-parse HEAD)" = 318615be3b8bbc60d1f6d52469ba5c0bdebed4f1
test "$(git -C /workspace/proofs-rs rev-parse HEAD)" = f6797340912a6231e55668a31b8b36746d4bc65c
if ! cargo proofs --version 2>/dev/null | rg -qx 'cargo proofs 0.3.4'; then
  cargo +1.91.0 install --locked --path /workspace/proofs-rs/cli
fi
cd /workspace/creusot
if ! cargo creusot version 2>/dev/null | rg -qx 'cargo-creusot 0.13.0'; then
  cargo install --locked --path cargo-creusot
fi
if [ ! -x /workspace/.local/share/creusot/toolchains/nightly-2026-06-22/bin/creusot-rustc ]; then
  cargo install --locked --path creusot-rustc --root /workspace/.local/share/creusot/toolchains/nightly-2026-06-22
fi
cargo run --locked --bin creusot-install -- prelude provers why3-conf --provers-parallelism 2
if [ ! -f /workspace/.opam/config ]; then
  opam init --bare --no-setup -y --disable-sandboxing default https://github.com/ocaml/opam-repository.git
fi
# The outer cloud task already supplies isolation; nested bwrap is unavailable.
opam --cli=2.1 var --global in-creusot-ci=true
if [ ! -d /workspace/.local/share/creusot/_opam/.opam-switch ]; then
  opam switch create -y --empty /workspace/.local/share/creusot
fi
opam install -y --no-depexts --switch=/workspace/.local/share/creusot ocaml-base-compiler.5.3.0
# Same upstream commit, obtained through official archive and API endpoints.
if [ ! -f /workspace/.setup/why3-source.tar.gz ]; then
  curl --fail --location --max-time 600 'https://gitlab.inria.fr/why3/why3/-/archive/54c92f96bb0711d6e991c18f10bfbc08d90d028b/why3-54c92f96bb0711d6e991c18f10bfbc08d90d028b.tar.gz' -o /workspace/.setup/why3-source.tar.gz
fi
printf '%s\n' 'c4b57a5904ac4f52b815028cbade036540270a82f75e12a1cae3d49a4f8d5a81  /workspace/.setup/why3-source.tar.gz' | sha256sum -c -
mkdir -p /workspace/.setup/why3-source
tar -xzf /workspace/.setup/why3-source.tar.gz --strip-components=1 -C /workspace/.setup/why3-source
# GitLab export-ignore omits Opam metadata; fetch it from the same commit.
mkdir -p /workspace/.setup/why3-source/opam
for package in why3 why3-ide; do
  curl --fail --location --max-time 60 "https://gitlab.inria.fr/api/v4/projects/why3%2Fwhy3/repository/files/opam%2F${package}.opam/raw?ref=54c92f96bb0711d6e991c18f10bfbc08d90d028b" -o "/workspace/.setup/why3-source/opam/${package}.opam"
done
test "$(git hash-object /workspace/.setup/why3-source/opam/why3.opam)" = d6262582d6375722a0b7552c89928749bdfd012d
test "$(git hash-object /workspace/.setup/why3-source/opam/why3-ide.opam)" = 6c87545bd1dc603a08d3202a25b4ae6e5b06dcfd
opam pin add --no-action -y --switch=/workspace/.local/share/creusot why3.git-54c92f96 /workspace/.setup/why3-source
opam pin add --no-action -y --switch=/workspace/.local/share/creusot why3-ide.git-54c92f96 /workspace/.setup/why3-source
opam pin add --no-action -y --switch=/workspace/.local/share/creusot why3find.git-eab37557 'git+https://github.com/creusot-rs/why3find.git#eab37557d3e24e1913a3c4f44bc5528ef497c6c9'
# System prerequisites were installed locally; keep all Opam build probes.
# Exact source pins above replace automatic GitLab pin-depends retrieval.
OPAMNODEPEXTS=true OPAMIGNOREPINDEPENDS=true cargo run --locked --bin creusot-install -- why3
cargo proofs --version
cargo creusot version
/workspace/.local/share/creusot/bin/why3 --version
/workspace/.local/share/creusot/bin/why3find --version
# Bootstrap scope: this script installs tools only; project verification is separate.

cat > /workspace/.setup/check.sh <<'CHECK'
#!/usr/bin/env bash
set -euo pipefail
source /workspace/.setup/activate.sh
cargo proofs --version
cargo creusot version
for tool in why3 why3find; do
  if [ ! -x "/workspace/.local/share/creusot/bin/$tool" ]; then
    echo "Missing $tool: save network changes in environment settings, then run the Creusot why3 installation step." >&2
    exit 1
  fi
  "/workspace/.local/share/creusot/bin/$tool" --version
done
cd /workspace/.setup
if [ ! -d toolchain-smoke ]; then cargo creusot new toolchain-smoke; fi
cd toolchain-smoke
if [ -d verif ]; then find verif -type f -name proof.json -delete; fi
cargo creusot --no-cache
# A successful process alone is insufficient: require fresh, proved sessions.
python3 - <<'PY'
import json,pathlib
files=list(pathlib.Path('verif').rglob('proof.json'))
assert files, 'No proof.json produced'
def proved(v):
 if not isinstance(v,dict): return False
 if isinstance(v.get('prover'),str): return True
 if isinstance(v.get('tactic'),str):
  children=v.get('children')
  return isinstance(children,list) and bool(children) and all(map(proved,children))
 return bool(v) and all(isinstance(a,list) and bool(a) and all(map(proved,a)) for a in v.values())
count=0
for p in files:
 data=json.loads(p.read_text())
 modules=data.get('proofs')
 assert isinstance(modules,dict) and modules, p
 for module,goals in modules.items():
  for goal,tree in goals.items():
   assert proved(tree), (p,module,goal,tree)
   count+=1
assert count>0, 'No goals checked'
print(f'{count} bootstrap sample goals proved; no project verification run')
PY
CHECK
bash /workspace/.setup/check.sh
opam switch export --full --switch=/workspace/.local/share/creusot /workspace/.setup/creusot-switch.export
