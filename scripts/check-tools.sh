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
