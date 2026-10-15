#!/usr/bin/env bash
set -uo pipefail

version_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
repo_dir=$(cd -- "$version_dir/../.." && pwd)
probe_dir="$version_dir/verification/trial/probes"
result_root="$version_dir/verification/trial/probe-results"
cd "$probe_dir"
source "$repo_dir/scripts/activate.sh"

mkdir -p "$result_root/logs" || exit 1
run_dir=$(mktemp -d "$result_root/logs/run-XXXXXXXX") || exit 1
[[ -n "$run_dir" && -d "$run_dir" ]] || exit 1
run_id=${run_dir##*/}
printf 'Probe logs: %s\n' "$run_dir"
python3 - "$version_dir" "$probe_dir" "$run_dir" <<'PY' || exit 1
import hashlib, json, sys
from pathlib import Path
version, probe, run = map(Path, sys.argv[1:])
repo = version.parents[1]
inputs = [probe / "Cargo.toml", probe / "Cargo.lock", probe / "src/lib.rs", probe / "run.sh",
          probe / "why3find.json", version / "crate/src/date.rs", repo / "rust-toolchain.toml",
          repo / "scripts/activate.sh", repo / "why3find.json",
          Path("/workspace/creusot/creusot-std/src/std/time.rs"),
          Path("/workspace/creusot/creusot-std/src/std/fmt.rs"),
          Path("/workspace/creusot/creusot-std/src/std/string.rs"),
          Path("/workspace/creusot/creusot-std/src/std/cmp.rs"),
          Path("/workspace/creusot/creusot-std/src/std/io.rs")]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
(run / "inputs-before.json").write_text(json.dumps({str(p): sha(p) for p in inputs}, indent=2) + "\n")
PY

features=(probe-duration probe-system-time probe-utf8 probe-string probe-formatter)
targets=(duration_parts epoch_seconds ascii_is_utf8 ascii_trimmed_empty formatter_write)
state_file="$run_dir/status.tsv"

for index in "${!features[@]}"; do
  feature=${features[$index]}
  target=${targets[$index]}
  feature_dir="$run_dir/$feature"
  # cargo-creusot requires output paths to remain within this workspace.
  coma_dir="$probe_dir/verif/feature-run-$run_id/$feature/coma"
  mkdir -p "$feature_dir" "$coma_dir"
  clean_log="$feature_dir/clean.log"
  compile_log="$feature_dir/compile.log"
  prove_log="$feature_dir/prove.log"

  printf 'FEATURE: %s\nCOMMAND: cargo +nightly-2026-06-22 clean --target-dir target/creusot -p httpdate-api-probes\n' "$feature" > "$clean_log"
  if cargo +nightly-2026-06-22 clean --target-dir target/creusot -p httpdate-api-probes >> "$clean_log" 2>&1; then
    clean_exit=0
  else
    clean_exit=$?
  fi
  printf 'clean exit: %s\n' "$clean_exit" >> "$clean_log"

  compile_cmd=(cargo creusot --only=coma --span-mode off --output-dir "$coma_dir" -- --locked --features "$feature")
  printf 'FEATURE: %s\nCOMMAND:' "$feature" > "$compile_log"
  printf ' %q' "${compile_cmd[@]}" >> "$compile_log"
  printf '\n' >> "$compile_log"
  printf '[%s] compiling Creusot specs\n' "$feature"
  if "${compile_cmd[@]}" 2>&1 | tee -a "$compile_log"; then
    compile_exit=0
  else
    compile_exit=$?
  fi
  printf 'compile exit: %s\n' "$compile_exit" | tee -a "$compile_log"

  proof_exit=-
  proof_status=not_run_compile_failed
  coma_path=
  proof_json_path=
  goal_count=0
  target_vc=false
  all_proved=false

  if [ "$compile_exit" -eq 0 ]; then
    mapfile -t coma_files < <(find "$coma_dir" -type f -name "$target.coma" -print)
    if [ "${#coma_files[@]}" -eq 1 ]; then
      coma_path=${coma_files[0]}
      prove_cmd=(timeout --signal=TERM --kill-after=5s 60s cargo creusot --only=prove --no-cache --why3find-arg=-d --why3find-arg=1 "$coma_path")
      printf 'FEATURE: %s\nCOMMAND:' "$feature" > "$prove_log"
      printf ' %q' "${prove_cmd[@]}" >> "$prove_log"
      printf '\nTIME LIMIT: 60 seconds\n' >> "$prove_log"
      printf '[%s] proving %s\n' "$feature" "$coma_path"
      if "${prove_cmd[@]}" 2>&1 | tee -a "$prove_log"; then
        proof_exit=0
      else
        proof_exit=$?
      fi
      printf 'prove exit: %s\n' "$proof_exit" | tee -a "$prove_log"

      mapfile -t proof_files < <(find "$coma_dir" -type f -name proof.json -print)
      if [ "${#proof_files[@]}" -eq 1 ]; then
        proof_json_path=${proof_files[0]}
        analysis=$(python3 - "$proof_json_path" "$target" <<'PY'
import json
import sys

path, target = sys.argv[1:]

def proved(tree):
    if not isinstance(tree, dict):
        return False
    if isinstance(tree.get("prover"), str):
        return bool(tree["prover"])
    if isinstance(tree.get("tactic"), str):
        children = tree.get("children")
        return isinstance(children, list) and bool(children) and all(map(proved, children))
    return bool(tree) and all(
        isinstance(children, list) and bool(children) and all(map(proved, children))
        for children in tree.values()
    )

try:
    proofs = json.load(open(path, encoding="utf-8")).get("proofs")
    if not isinstance(proofs, dict):
        raise ValueError("missing proofs object")
    goals = {f"{module}.{goal}": tree for module, group in proofs.items()
             for goal, tree in group.items()}
    has_target = any(name.endswith(f".vc_{target}") for name in goals)
    resolved = bool(goals) and all(map(proved, goals.values()))
    print(f"{len(goals)}\t{str(has_target).lower()}\t{str(resolved).lower()}")
except Exception as exc:
    print(f"ERROR: {exc}", file=sys.stderr)
    sys.exit(2)
PY
        )
        analysis_exit=$?
        if [ "$analysis_exit" -eq 0 ]; then
          IFS=$'\t' read -r goal_count target_vc all_proved <<< "$analysis"
          if [ "$target_vc" = true ] && [ "$all_proved" = true ] && [ "$goal_count" -gt 0 ] && [ "$proof_exit" -eq 0 ]; then
            proof_status=all_goals_proved
          elif [ "$goal_count" -eq 0 ]; then
            proof_status=zero_goals_not_proof
          elif [ "$target_vc" != true ]; then
            proof_status=target_vc_missing
          else
            proof_status=unproved_or_nonzero_exit
          fi
        else
          proof_status=proof_json_invalid
        fi
      else
        proof_status=proof_json_missing_or_ambiguous
      fi
    else
      proof_status=target_coma_missing_or_ambiguous
    fi
  fi

  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$feature" "$target" "$clean_exit" "$compile_exit" "$proof_exit" "$proof_status" \
    "$coma_path" "$proof_json_path" "$goal_count" "$target_vc" "$all_proved" >> "$state_file"
  printf '[%s] compile=%s proof=%s goals=%s target_vc=%s all_proved=%s\n' \
    "$feature" "$compile_exit" "$proof_status" "$goal_count" "$target_vc" "$all_proved"
done

python3 - "$version_dir" "$probe_dir" "$run_dir" "$state_file" <<'PY'
import datetime
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

version_dir, probe_dir, run_dir, state_file = map(Path, sys.argv[1:])
repo_dir = version_dir.parents[1]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

inputs = [
    probe_dir / "Cargo.toml",
    probe_dir / "Cargo.lock",
    probe_dir / "src/lib.rs",
    probe_dir / "run.sh",
    probe_dir / "why3find.json",
    version_dir / "crate/src/date.rs",
    repo_dir / "rust-toolchain.toml",
    repo_dir / "scripts/activate.sh",
    repo_dir / "why3find.json",
    Path("/workspace/creusot/creusot-std/src/std/time.rs"),
    Path("/workspace/creusot/creusot-std/src/std/fmt.rs"),
    Path("/workspace/creusot/creusot-std/src/std/string.rs"),
    Path("/workspace/creusot/creusot-std/src/std/cmp.rs"),
    Path("/workspace/creusot/creusot-std/src/std/io.rs"),
]

versions = {}
version_commands = {
    "cargo_creusot": ["cargo", "creusot", "version"],
    "cargo_proofs": ["cargo", "proofs", "--version"],
    "rustc": ["rustc", "--version"],
    "why3": ["why3", "--version"],
    "why3find": ["why3find", "--version"],
    "alt_ergo": ["alt-ergo", "--version"],
    "z3": ["z3", "--version"],
    "cvc5": ["cvc5", "--version"],
    "cvc4": ["cvc4", "--version"],
}
for label, command in version_commands.items():
    try:
        result = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=15)
        versions[label] = {"exit": result.returncode, "output": result.stdout.strip()}
    except Exception as exc:
        versions[label] = {"error": str(exc)}

tool_binary_sha256 = {}
for label, binary in {
    "cargo": "cargo",
    "cargo_creusot": "cargo-creusot",
    "cargo_proofs": "cargo-proofs",
    "rustc": "rustc",
    "why3": "why3",
    "why3find": "why3find",
    "alt_ergo": "alt-ergo",
    "z3": "z3",
    "cvc5": "cvc5",
    "cvc4": "cvc4",
}.items():
    located = shutil.which(binary)
    tool_binary_sha256[label] = (
        {"path": located, "sha256": sha(Path(located))} if located else None
    )

features = []
for line in state_file.read_text().splitlines():
    fields = line.split("\t")
    (feature, target, clean_exit, compile_exit, proof_exit, proof_status,
     coma, proof_json, goals, target_vc, all_proved) = fields
    feature_record = {
        "feature": feature,
        "target": target,
        "clean_exit": int(clean_exit),
        "compile_exit": int(compile_exit),
        "proof_exit": None if proof_exit == "-" else int(proof_exit),
        "proof_status": proof_status,
        "coma_path": str(Path(coma).relative_to(version_dir)) if coma else None,
        "proof_json_path": str(Path(proof_json).relative_to(version_dir)) if proof_json else None,
        "session_goals": int(goals),
        "target_vc_present": target_vc == "true",
        "all_goal_trees_proved": all_proved == "true",
        "claim_scope": {
            "probe-duration": "seconds and subsecond nanoseconds reconstruct Duration's modeled nanosecond value",
            "probe-system-time": "translation/panic behavior only; no semantic contract was added",
            "probe-utf8": "requires each byte < 128 and ensures UTF-8 validation succeeds",
            "probe-string": "translation/panic behavior only; no semantic contract was added",
            "probe-formatter": "translation/panic behavior only; Formatter output content is not specified",
        }[feature],
        "logs": {name: str((run_dir / feature / f"{name}.log").relative_to(version_dir))
                 for name in ("clean", "compile", "prove")},
    }
    preserved = []
    if coma and proof_json:
        source_coma, source_proof = version_dir / coma, version_dir / proof_json
        archive = version_dir / "verification/trial/probe-results/artifacts" / run_dir.name / feature
        archive.mkdir(parents=True, exist_ok=True)
        archived_coma, archived_proof = archive / "target.coma", archive / "proof.json"
        shutil.copy2(source_coma, archived_coma)
        shutil.copy2(source_proof, archived_proof)
        preserved.append({"name": "target", "coma": str(archived_coma.relative_to(version_dir)),
                          "proof_json": str(archived_proof.relative_to(version_dir)),
                          "coma_sha256": sha(archived_coma),
                          "proof_json_sha256": sha(archived_proof)})
    feature_record["preserved_artifacts"] = preserved
    features.append(feature_record)

inputs_before = json.loads((run_dir / "inputs-before.json").read_text())
input_hashes_after = {str(path): sha(path) for path in map(Path, inputs_before)}

summary = {
    "generated_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "scope": "Five independent Creusot std API probes; no httpdate implementation changes or whole-API claims.",
    "toolchain_commit": subprocess.run(["git", "-C", "/workspace/creusot", "rev-parse", "HEAD"],
                                       text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout.strip(),
    "versions": versions,
    "tool_binary_sha256": tool_binary_sha256,
    "input_sha256": inputs_before,
    "input_hash_snapshot": str((run_dir / "inputs-before.json").relative_to(version_dir)),
    "input_sha256_after_proof": input_hashes_after,
    "inputs_unchanged_during_run": {path: inputs_before[path] == input_hashes_after[path]
                                     for path in inputs_before},
    "probe_command": "cargo creusot --only=coma --span-mode off --output-dir <fresh-run>/coma -- --locked --features <feature>",
    "proof_command": "timeout --signal=TERM --kill-after=5s 60s cargo creusot --only=prove --no-cache --why3find-arg=-d --why3find-arg=1 <exact-target-coma>",
    "features": features,
}
output = version_dir / "verification/trial/probe-results/summary.json"
output.parent.mkdir(parents=True, exist_ok=True)
output.write_text(json.dumps(summary, indent=2) + "\n")
print(f"Summary: {output}")
PY
