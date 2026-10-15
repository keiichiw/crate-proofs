#!/usr/bin/env bash
set -uo pipefail
version_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
repo_dir=$(cd -- "$version_dir/../.." && pwd)
probe_dir="$version_dir/verification/trial/trait-probes"
result_root="$version_dir/verification/trial/trait-probe-results"
cd "$probe_dir"
source "$repo_dir/scripts/activate.sh"
mkdir -p "$result_root/logs" || exit 1
run_dir=$(mktemp -d "$result_root/logs/run-XXXXXXXX") || exit 1
[[ -n "$run_dir" && -d "$run_dir" ]] || exit 1
run_id=${run_dir##*/}
python3 - "$version_dir" "$probe_dir" "$run_dir" <<'PY' || exit 1
import hashlib, json, sys
from pathlib import Path
version, probe, run = map(Path, sys.argv[1:])
repo = version.parents[1]
inputs = [probe / "Cargo.toml", probe / "Cargo.lock", probe / "src/lib.rs", probe / "run.sh",
          probe / "why3find.json", repo / "rust-toolchain.toml", repo / "scripts/activate.sh"]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
(run / "inputs-before.json").write_text(json.dumps({str(p): sha(p) for p in inputs}, indent=2) + "\n")
PY
features=(probe-eq probe-ord probe-hash probe-error)
targets=(structural_eq chronological_cmp hash_via_default_hasher into_io_error)
state="$run_dir/status.tsv"
for i in "${!features[@]}"; do
  feature=${features[$i]}; target=${targets[$i]}; fdir="$run_dir/$feature"; mkdir -p "$fdir"
  clean_log="$fdir/clean.log"; compile_log="$fdir/compile.log"; prove_log="$fdir/prove.log"
  if cargo +nightly-2026-06-22 clean --target-dir target/creusot -p httpdate-trait-probes >"$clean_log" 2>&1; then ce=0; else ce=$?; fi
  coma_dir="$probe_dir/verif/trait-run-$run_id/$feature/coma"; mkdir -p "$coma_dir"
  cmd=(cargo creusot --only=coma --span-mode off --output-dir "$coma_dir" -- --locked --features "$feature")
  printf 'COMMAND:' >"$compile_log"; printf ' %q' "${cmd[@]}" >>"$compile_log"; printf '\n' >>"$compile_log"
  if "${cmd[@]}" >>"$compile_log" 2>&1; then co=0; else co=$?; fi
  pe=-; status=not_run_compile_failed; goals=0; targetvc=false; proved=false; coma=; proofjson=
  if [[ $co == 0 ]]; then
    mapfile -t files < <(find "$coma_dir" -type f -name "$target.coma" -print)
    if [[ ${#files[@]} == 1 ]]; then
      coma=${files[0]}
      pc=(timeout --signal=TERM --kill-after=5s 60s cargo creusot --only=prove --no-cache --why3find-arg=-d --why3find-arg=1 "$coma")
      printf 'COMMAND:' >"$prove_log"; printf ' %q' "${pc[@]}" >>"$prove_log"; printf '\n' >>"$prove_log"
      if "${pc[@]}" >>"$prove_log" 2>&1; then pe=0; else pe=$?; fi
      mapfile -t js < <(find "$coma_dir" -type f -name proof.json -print)
      if [[ ${#js[@]} == 1 ]]; then
        proofjson=${js[0]}
        read -r goals targetvc proved < <(python3 - "$proofjson" "$target" <<'PY'
import json,sys
p,t=sys.argv[1:]
def ok(x):
 if not isinstance(x,dict): return False
 if isinstance(x.get('prover'),str): return bool(x['prover'])
 if isinstance(x.get('tactic'),str): return bool(x.get('children')) and all(map(ok,x['children']))
 return bool(x) and all(isinstance(v,list) and bool(v) and all(map(ok,v)) for v in x.values())
groups=json.load(open(p)).get('proofs')
if not isinstance(groups,dict): raise SystemExit(2)
g={f'{m}.{n}':v for m,x in groups.items() for n,v in x.items()}
print(len(g),str(any(n.endswith('.vc_'+t) or n.endswith('.vc_'+t+'_T') for n in g)).lower(),str(bool(g) and all(map(ok,g.values()))).lower())
PY
)
        if [[ $targetvc == true && $proved == true && $goals -gt 0 && $pe == 0 ]]; then status=all_goals_proved
        elif [[ $goals == 0 ]]; then status=zero_goals_not_proof
        elif [[ $targetvc != true ]]; then status=target_vc_missing
        else status=unproved_or_nonzero_exit; fi
      else status=proof_json_missing_or_ambiguous; fi
    else status=target_coma_missing_or_ambiguous; fi
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$feature" "$target" "$ce" "$co" "$pe" "$status" "$coma" "$proofjson" "$goals" "$targetvc" "$proved" >>"$state"
done
python3 - "$version_dir" "$probe_dir" "$run_dir" "$state" <<'PY'
import datetime,hashlib,json,shutil,subprocess,sys
from pathlib import Path
version,probe,run,state=map(Path,sys.argv[1:])
repo=version.parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
inputs=[probe/'Cargo.toml',probe/'Cargo.lock',probe/'src/lib.rs',probe/'run.sh',probe/'why3find.json',repo/'rust-toolchain.toml',repo/'scripts/activate.sh']
features=[]
for line in state.read_text().splitlines():
 f,t,clean,compile,proof,status,coma,pj,goals,target,proved=line.split('\t')
 record=dict(feature=f,target=t,clean_exit=int(clean),compile_exit=int(compile),proof_exit=None if proof=='-' else int(proof),proof_status=status,session_goals=int(goals),target_vc_present=target=='true',all_goal_trees_proved=proved=='true',coma_path=str(Path(coma).relative_to(version)) if coma else None,proof_json_path=str(Path(pj).relative_to(version)) if pj else None,logs={n:str((run/f/f'{n}.log').relative_to(version)) for n in ['clean','compile','prove']},claim_scope={'probe-eq':'derived structural PartialEq against a derived DeepModel','probe-ord':'lexicographic ordering logic and Rust Ord against tuple key','probe-hash':'Hash call path through DefaultHasher; any proof only covers generated goals, not the hash law','probe-error':'Error Display implementation and conversion into io::Error'}[f])
 artifacts=[]
 if coma and pj:
  src_coma,src_proof=version/coma,version/pj
  archive=version/'verification/trial/trait-probe-results/artifacts'/run.name/f
  archive.mkdir(parents=True,exist_ok=True)
  c_dst,p_dst=archive/'target.coma',archive/'proof.json'
  shutil.copy2(src_coma,c_dst); shutil.copy2(src_proof,p_dst)
  artifacts.append(dict(name='target',coma=str(c_dst.relative_to(version)),proof_json=str(p_dst.relative_to(version)),coma_sha256=sha(c_dst),proof_json_sha256=sha(p_dst)))
 record['preserved_artifacts']=artifacts
 features.append(record)
versions={}
for k,c in {'cargo_creusot':['cargo','creusot','version'],'rustc':['rustc','--version'],'why3':['why3','--version'],'why3find':['why3find','--version']}.items():
 r=subprocess.run(c,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT); versions[k]={'exit':r.returncode,'output':r.stdout.strip()}
before=json.loads((run/'inputs-before.json').read_text()); after={str(p):sha(p) for p in map(Path,before)}
summary={'generated_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Independent trait probes; no httpdate APIs or production source were verified.','toolchain_commit':subprocess.run(['git','-C','/workspace/creusot','rev-parse','HEAD'],text=True,stdout=subprocess.PIPE).stdout.strip(),'versions':versions,'input_sha256':before,'input_hash_snapshot':str((run/'inputs-before.json').relative_to(version)),'input_sha256_after_proof':after,'inputs_unchanged_during_run':{p:before[p]==after[p] for p in before},'compile_command':'cargo creusot --only=coma --span-mode off --output-dir <fresh-run>/coma -- --locked --features <feature>','proof_command':'timeout --signal=TERM --kill-after=5s 60s cargo creusot --only=prove --no-cache --why3find-arg=-d --why3find-arg=1 <exact-target-coma>','features':features}
out=version/'verification/trial/trait-probe-results/summary.json'; out.write_text(json.dumps(summary,indent=2)+'\n'); print(out)
PY
