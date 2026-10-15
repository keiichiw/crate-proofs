# Source from Bash or Zsh to use this checkout's isolated macOS verification tools.
if [ -n "${BASH_VERSION:-}" ]; then
  _proof_activate_path=${BASH_SOURCE[0]}
elif [ -n "${ZSH_VERSION:-}" ]; then
  eval '_proof_activate_path=${(%):-%x}'
else
  echo 'activate-local.sh requires Bash or Zsh' >&2
  return 1
fi
PROOF_LOCAL_ROOT=$(cd -- "$(dirname -- "$_proof_activate_path")/.." && pwd)/.local-verification
export PROOF_LOCAL_ROOT
export CARGO_HOME="$PROOF_LOCAL_ROOT/cargo"
export RUSTUP_HOME="$PROOF_LOCAL_ROOT/rustup"
export OPAMROOT="$PROOF_LOCAL_ROOT/opam"
export XDG_DATA_HOME="$PROOF_LOCAL_ROOT/share"
export XDG_CONFIG_HOME="$PROOF_LOCAL_ROOT/config"
export XDG_CACHE_HOME="$PROOF_LOCAL_ROOT/cache"
export CREUSOT_DATA_HOME="$XDG_DATA_HOME/creusot"
export PATH="$CARGO_HOME/bin:$CREUSOT_DATA_HOME/bin:$PATH"
export CARGO_BUILD_JOBS=2
export OPAMJOBS=2
export RUSTUP_NO_UPDATE_CHECK=1
unset _proof_activate_path
