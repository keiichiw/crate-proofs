#!/usr/bin/env bash
set -euo pipefail
repo_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
source "$repo_dir/scripts/activate-local.sh"
mkdir -p "$PROOF_LOCAL_ROOT/smoke"
run_dir=$(mktemp -d "$PROOF_LOCAL_ROOT/smoke/run-XXXXXXXX")
cd "$run_dir"
{
  uname -srm
  cargo +1.91.0 proofs --version
  cargo +1.91.0 creusot version
  rustc +1.91.0 -Vv
  rustc +nightly-2026-06-22 -Vv
} | tee versions.txt
creusot_version=$(cargo +1.91.0 creusot version)
[[ ${creusot_version%%$'\n'*} == 'cargo-creusot 0.13.0' ]]
cargo +1.91.0 creusot new sample
cd sample
cargo +1.91.0 creusot --no-cache 2>&1 | tee ../prove.log
python3 - "$run_dir" <<'PY'
import hashlib, json, pathlib, shutil, subprocess, sys
run = pathlib.Path(sys.argv[1])
files = sorted(pathlib.Path('verif').rglob('proof.json'))
assert files, 'No proof sessions generated'
def proved(tree):
    if not isinstance(tree, dict): return False
    if isinstance(tree.get('prover'), str): return bool(tree['prover'])
    if isinstance(tree.get('tactic'), str):
        children = tree.get('children')
        return isinstance(children, list) and bool(children) and all(map(proved, children))
    return bool(tree) and all(isinstance(v, list) and bool(v) and all(map(proved, v)) for v in tree.values())
count = 0
for path in files:
    modules = json.loads(path.read_text()).get('proofs')
    assert isinstance(modules, dict) and modules, path
    for module, goals in modules.items():
        assert goals, (path, module)
        for goal, tree in goals.items():
            assert proved(tree), (path, module, goal)
            count += 1
assert count > 0, 'No positive proved goals'
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
tools = {}
for tool in ('cargo-creusot', 'cargo-proofs', 'why3', 'why3find', 'alt-ergo', 'z3', 'cvc4', 'cvc5'):
    path = pathlib.Path(shutil.which(tool)).resolve()
    tools[tool] = {'path': str(path), 'sha256': sha(path)}
record = {'status': 'passed', 'scope': 'Fresh bootstrap sample only; no crate verification claim',
          'host': subprocess.check_output(['uname', '-srm'], text=True).strip(),
          'closed_session_goals': count, 'tools': tools,
          'proof_sessions': {str(p): sha(p) for p in files}}
(run / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
print(f'{count} bootstrap sample goals proved; no repository crate proof was run. Evidence: {run}')
PY
