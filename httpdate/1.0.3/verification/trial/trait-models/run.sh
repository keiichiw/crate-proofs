#!/usr/bin/env bash
set -uo pipefail
version_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
repo_dir=$(cd -- "$version_dir/../.." && pwd)
probe_dir="$version_dir/verification/trial/trait-models"
result_root="$version_dir/verification/trial/trait-model-results"
cd "$probe_dir"
source "$repo_dir/scripts/activate.sh"
mkdir -p "$result_root/logs" || exit 1
run_dir=$(mktemp -d "$result_root/logs/run-XXXXXXXX")
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
features=(model-eq model-ord)
targets=(structural_eq chronological_cmp)
state="$run_dir/status.tsv"
for i in "${!features[@]}"; do
  feature=${features[$i]}; target=${targets[$i]}; fdir="$run_dir/$feature"; mkdir -p "$fdir"
  native_log="$fdir/native-tests.log"
  if cargo test --locked --features "$feature" >"$native_log" 2>&1; then native_exit=0; else native_exit=$?; fi
  printf 'COMMAND: cargo test --locked --features %q\nEXIT: %s\n' "$feature" "$native_exit" >>"$native_log"
  native_tests=$(sed -nE 's/^running ([0-9]+) tests?$/\1/p' "$native_log" | awk '{n += $1} END {print n+0}')

  clean_log="$fdir/clean.log"
  if cargo +nightly-2026-06-22 clean --target-dir target/creusot -p httpdate-trait-model-probes >"$clean_log" 2>&1; then clean_exit=0; else clean_exit=$?; fi
  coma_dir="$probe_dir/verif/model-run-$run_id/$feature/coma"; mkdir -p "$coma_dir"
  compile_log="$fdir/compile.log"
  compile=(cargo creusot --only=coma --span-mode off --output-dir "$coma_dir" -- --locked --features "$feature")
  printf 'COMMAND:' >"$compile_log"; printf ' %q' "${compile[@]}" >>"$compile_log"; printf '\n' >>"$compile_log"
  if "${compile[@]}" >>"$compile_log" 2>&1; then compile_exit=0; else compile_exit=$?; fi

  files=0; goals=0; failed_goals=0; failed_files=0; target_found=false
  proof_status=not_run_compile_failed
  if [[ $compile_exit -eq 0 ]]; then
    proof_status=all_selected_coma_processed
    mapfile -t coma_files < <(find "$coma_dir" -type f -name '*.coma' -print | sort)
    files=${#coma_files[@]}
    if [[ $files -eq 0 ]]; then proof_status=no_coma_files; fi
    for coma in "${coma_files[@]}"; do
      base=$(basename "$coma" .coma)
      proof_log="$fdir/prove-$base.log"
      prove=(timeout --signal=TERM --kill-after=5s 60s cargo creusot --only=prove --no-cache --why3find-arg=-d --why3find-arg=2 "$coma")
      printf 'COMMAND:' >"$proof_log"; printf ' %q' "${prove[@]}" >>"$proof_log"; printf '\nTIME LIMIT: 60 seconds\n' >>"$proof_log"
      if "${prove[@]}" >>"$proof_log" 2>&1; then proof_exit=0; else proof_exit=$?; fi
      json="$coma_dir/verif/httpdate_trait_model_probes_rlib"
      proof_json="$(dirname "$coma")/$base/proof.json"
      read -r count matched resolved < <(python3 - "$proof_json" "$target" "$base" <<'PY'
import json,sys
path,target,base=sys.argv[1:]
def ok(tree):
 if not isinstance(tree,dict): return False
 if isinstance(tree.get('prover'),str): return bool(tree['prover'])
 if isinstance(tree.get('tactic'),str): return bool(tree.get('children')) and all(map(ok,tree['children']))
 return bool(tree) and all(isinstance(v,list) and bool(v) and all(map(ok,v)) for v in tree.values())
try:
 ps=json.load(open(path,encoding='utf-8')).get('proofs')
 if not isinstance(ps,dict): raise ValueError('missing proofs')
 goals={f'{m}.{g}':v for m,group in ps.items() for g,v in group.items()}
 matched=any(n.endswith('.vc_'+target) or n.endswith('.vc_'+target+'_T') for n in goals)
 print(len(goals),str(matched).lower(),str(bool(goals) and all(map(ok,goals.values()))).lower())
except Exception:
 print('0 false false')
PY
)
      goals=$((goals + count))
      [[ $matched == true ]] && target_found=true
      if [[ $count -eq 0 || $resolved != true || $proof_exit -ne 0 ]]; then
        failed_files=$((failed_files + 1))
        failed_goals=$((failed_goals + count))
      fi
      printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$base" "$proof_exit" "$count" "$matched" "$resolved" "$coma" "$proof_json" >>"$fdir/coma-results.tsv"
    done
    if [[ $native_exit -ne 0 || $native_tests -eq 0 || $clean_exit -ne 0 || $compile_exit -ne 0 ]]; then proof_status=required_check_failed
    elif [[ $files -eq 0 ]]; then proof_status=no_coma_files
    elif [[ $target_found != true ]]; then proof_status=target_vc_missing
    elif [[ $goals -eq 0 ]]; then proof_status=zero_goals_not_proof
    elif [[ $failed_files -eq 0 ]]; then proof_status=all_goal_trees_proved
    else proof_status=unproved_or_nonzero_exit; fi
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$feature" "$target" "$native_exit" "$native_tests" "$clean_exit" "$compile_exit" \
    "$proof_status" "$files" "$goals" "$target_found" "$failed_goals" "$failed_files" >>"$state"
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
 f,target,native,native_tests,clean,compile,status,nfiles,goals,target_found,failed,failed_files=line.split('\t')
 result_path=run/f/'coma-results.tsv'
 comas=[]
 if result_path.exists():
  for row in result_path.read_text().splitlines():
   name,exit_,count,matched,resolved,coma,pj=row.split('\t')
   coma_src,proof_src=Path(coma),Path(pj)
   artifact=dict(name=name,proof_exit=int(exit_),session_goals=int(count),target_vc_present=matched=='true',all_goal_trees_proved=resolved=='true',coma_path=str(coma_src.relative_to(version)),proof_json_path=str(proof_src.relative_to(version)),proof_log=str((run/f/f'prove-{name}.log').relative_to(version)))
   if coma_src.is_file() and proof_src.is_file():
    archive=version/'verification/trial/trait-model-results/artifacts'/run.name/f/name
    archive.mkdir(parents=True,exist_ok=True)
    coma_dst,proof_dst=archive/'target.coma',archive/'proof.json'
    shutil.copy2(coma_src,coma_dst); shutil.copy2(proof_src,proof_dst)
    artifact.update(preserved_coma_path=str(coma_dst.relative_to(version)),preserved_proof_json_path=str(proof_dst.relative_to(version)),preserved_coma_sha256=sha(coma_dst),preserved_proof_json_sha256=sha(proof_dst))
   else:
    artifact['artifact_missing']=True
   comas.append(artifact)
 acceptance=(int(native)==0 and int(native_tests)>0 and int(clean)==0 and int(compile)==0 and status=='all_goal_trees_proved' and int(nfiles)>0 and len(comas)==int(nfiles) and int(goals)>0 and target_found=='true' and int(failed)==0 and int(failed_files)==0 and all(c['session_goals']>0 and c['proof_exit']==0 and c['all_goal_trees_proved'] for c in comas) and all('preserved_coma_path' in c for c in comas))
 features.append(dict(feature=f,target=target,native_test_exit=int(native),native_test_count=int(native_tests),clean_exit=int(clean),compile_exit=int(compile),proof_status=status,acceptance_passed=acceptance,coma_files=int(nfiles),session_goals=int(goals),target_vc_present=target_found=='true',failed_goal_count=int(failed),failed_file_count=int(failed_files),native_log=str((run/f/'native-tests.log').relative_to(version)),clean_log=str((run/f/'clean.log').relative_to(version)),compile_log=str((run/f/'compile.log').relative_to(version)),comas=comas))
versions={}
for k,c in {'cargo_creusot':['cargo','creusot','version'],'rustc':['rustc','--version'],'why3':['why3','--version'],'why3find':['why3find','--version']}.items():
 r=subprocess.run(c,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT); versions[k]={'exit':r.returncode,'output':r.stdout.strip()}
before=json.loads((run/'inputs-before.json').read_text()); after={str(p):sha(p) for p in map(Path,before)}
inputs_unchanged=all(before[p]==after[p] for p in before)
summary={'generated_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Positive structural-model probes for equality and chronological order; no httpdate source/API was changed or proved. Acceptance requires native tests, nonzero goals for every generated Coma, the named target VC, every goal tree proved, successful commands, preserved artifacts, and unchanged inputs.','acceptance_passed':inputs_unchanged and len(features)==2 and all(f['acceptance_passed'] for f in features),'toolchain_commit':subprocess.run(['git','-C','/workspace/creusot','rev-parse','HEAD'],text=True,stdout=subprocess.PIPE).stdout.strip(),'versions':versions,'input_sha256':before,'input_hash_snapshot':str((run/'inputs-before.json').relative_to(version)),'input_sha256_after_proof':after,'inputs_unchanged_during_run':{p:before[p]==after[p] for p in before},'native_command':'cargo test --locked --features <feature>','compile_command':'cargo creusot --only=coma --span-mode off --output-dir <fresh-run>/coma -- --locked --features <feature>','proof_command':'timeout --signal=TERM --kill-after=5s 60s cargo creusot --only=prove --no-cache --why3find-arg=-d --why3find-arg=2 <each-exact-coma-file>','features':features}
out=version/'verification/trial/trait-model-results/summary.json'; out.write_text(json.dumps(summary,indent=2)+'\n'); print(out)
if not summary['acceptance_passed']:
 sys.exit(1)
PY
