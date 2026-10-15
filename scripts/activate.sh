# Native macOS installation; keep the historical cloud environment below intact.
if [ "$(uname -s)" = Darwin ]; then
  if [ -n "${BASH_VERSION:-}" ]; then
    _proof_activate_file=${BASH_SOURCE[0]}
  else
    eval '_proof_activate_file=${(%):-%x}'
  fi
  source "$(dirname -- "$_proof_activate_file")/activate-local.sh"
  unset _proof_activate_file
  return 0
fi
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
