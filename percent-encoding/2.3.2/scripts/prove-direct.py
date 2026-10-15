#!/usr/bin/env python3
"""Prove selected fresh Creusot roots with direct Why3 exports, Z3, and CVC5 fallback."""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
VERSION = HERE.parent
REPO = VERSION.parent.parent
FORM = REPO / "form_urlencoded/1.2.2"
XDG = Path(os.environ.get("XDG_DATA_HOME", "/workspace/.local/share"))
CONF = XDG / "creusot/creusot_why3.conf"
LIB = XDG / "creusot/share/why3find/packages/creusot"


def need(ok, message):
    if not ok: raise ValueError(message)


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""): h.update(block)
    return h.hexdigest()


def run(cmd, timeout=120):
    return subprocess.run(cmd, cwd=VERSION, capture_output=True, text=True,
                          timeout=timeout, env=os.environ.copy())


def why3_base():
    return ["why3", "prove", "-C", str(CONF), "-L", str(LIB)]


def roots_for(coma):
    cmd = why3_base() + [str(coma)]
    result = run(cmd)
    roots, theory = [], None
    for line in result.stdout.splitlines():
        match = re.match(r"^theory (\S+)$", line)
        if match: theory = match.group(1)
        match = re.match(r"^  goal (\S+)\s*:", line)
        if match:
            need(theory is not None, f"goal lacks a theory in {coma}")
            roots.append((theory, match.group(1)))
    return cmd, result, roots


def save_process(bundle, root, name, cmd, proc):
    paths = {}
    for suffix, content in (("command.json", json.dumps(cmd, indent=2) + "\n"),
                            ("stdout.txt", proc.stdout), ("stderr.txt", proc.stderr)):
        path = root / f"{name}.{suffix}"
        path.write_text(content)
        paths[suffix] = path
    return {key: {"path": path.relative_to(bundle).as_posix(), "sha256": sha(path)}
            for key, path in paths.items()}


def fingerprint():
    import importlib.util
    spec = importlib.util.spec_from_file_location("check_proofs", HERE / "check-proofs.py")
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    return {str(p.relative_to(VERSION) if p.is_relative_to(VERSION) else p): sha(p)
            for p in helper.input_paths()}


def tool_fingerprint():
    import importlib.util
    spec = importlib.util.spec_from_file_location("check_proofs", HERE / "check-proofs.py")
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    return helper.tool_hashes()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--generated-dir", type=Path, required=True)
    ap.add_argument("--run-dir", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--time-limit", type=int, default=30)
    ap.add_argument("--cvc5-time-limit-ms", type=int, default=60_000)
    args = ap.parse_args()
    need(args.time_limit > 0, "time limit must be positive")
    need(args.cvc5_time_limit_ms > 0, "cvc5 time limit must be positive")
    cvc5 = shutil.which("cvc5")
    need(cvc5 is not None, "cvc5 is required on activated PATH as the secondary solver")
    generated, run_dir, out = args.generated_dir.resolve(), args.run_dir.resolve(), args.output.resolve()
    need(generated.is_dir(), f"fresh generated directory missing: {generated}")
    need(not out.exists(), f"output already exists: {out}")
    out.mkdir(parents=True)
    before_path = run_dir / "inputs-before.json"
    before_record = json.loads(before_path.read_text())
    before = fingerprint()
    need(before == before_record.get("inputs_sha256"), "pre-compile source snapshot mismatch")
    tools_before = tool_fingerprint()
    need(tools_before == before_record.get("tools_sha256"), "pre-compile tool snapshot mismatch")
    inventory = json.loads((VERSION / "verification/target-inventory.json").read_text())
    selected, opened, excluded = (inventory.get("selected", {}), inventory.get("expected_open", {}),
                                  inventory.get("excluded_generated", {}))
    need(isinstance(selected, dict) and selected, "target inventory has no selected targets")
    actual = {p.relative_to(generated).as_posix().removesuffix(".coma"): p
              for p in generated.rglob("*.coma")}
    classified = set(selected) | set(opened) | set(excluded)
    need(set(actual) == classified,
         f"generated target inventory mismatch: missing={sorted(classified-set(actual))}, extra={sorted(set(actual)-classified)}")
    encoder_coma = actual.get("percent_encode_byte")
    decoder_coma = actual.get("impl_PercentDecode_0/next_byte")
    need(encoder_coma and "encoded_array_model" in encoder_coma.read_text(errors="replace"),
         "encoder Coma does not contain its checked dependency call encoded_array_model")
    need(decoder_coma and "byte_model_subsequence" in decoder_coma.read_text(errors="replace"),
         "decoder Coma does not contain its checked dependency call byte_model_subsequence")
    source_calls = set()
    for source in (VERSION / "crate/src").rglob("*.rs"):
        source_calls.update(re.findall(r"\bform_model::([A-Za-z_][A-Za-z_0-9]*)", source.read_text()))
    need(source_calls and {"encoded_array_model", "byte_model_subsequence"} <= source_calls,
         "source lacks explicit checked form dependency calls")
    require_dependency_audit = run_dir / "dependency-audit.json"
    need(require_dependency_audit.is_file(), "pre-run dependency evidence audit is missing")
    dependency_audit = json.loads(require_dependency_audit.read_text())
    need(dependency_audit.get("status") == "passed", "pinned form dependency evidence audit failed")
    (out / "dependency-audit.json").write_bytes(require_dependency_audit.read_bytes())
    selected_records, smt_hashes, total_roots, closed_roots = {}, {}, 0, 0
    unresolved = []
    for name in selected:
        coma = actual[name]
        target_dir = out / "targets" / name
        target_dir.mkdir(parents=True)
        list_cmd, listed, roots = roots_for(coma)
        listlog = save_process(out, target_dir, "root-listing", list_cmd, listed)
        need(listed.returncode == 0, f"Why3 root listing failed for {name}: {listed.stderr}")
        need(roots and len(roots) == len(set(roots)), f"selected target has no unique roots: {name}")
        mapped = []
        target_closed = 0
        target_open = []
        for index, (theory, goal) in enumerate(roots):
            root_id = f"{index:04d}-{theory}-{goal}"
            root_dir = target_dir / "roots" / root_id
            export_dir = root_dir / "export"
            export_dir.mkdir(parents=True)
            base = why3_base() + [str(coma), "-T", theory, "-G", goal]
            export_cmd = base + ["-a", "compute_specified", "-a", "split_vc", "-P", "Z3", "-o", str(export_dir)]
            exported = run(export_cmd)
            export_log = save_process(out, root_dir, "why3-export", export_cmd, exported)
            need(exported.returncode == 0, f"Why3 export failed at {name}:{theory}.{goal}: {exported.stderr}")
            smts = sorted(export_dir.rglob("*.smt2"))
            export_mode = "transformed"
            if not smts:
                baseline_dir = root_dir / "untransformed-export"
                baseline_dir.mkdir()
                raw_cmd = base + ["-P", "Z3", "-o", str(baseline_dir)]
                raw = run(raw_cmd)
                raw_log = save_process(out, root_dir, "untransformed-export", raw_cmd, raw)
                need(raw.returncode == 0, f"untransformed export failed at {name}:{theory}.{goal}")
                smts = sorted(baseline_dir.rglob("*.smt2"))
                export_mode = "untransformed-positive-root"
                export_log = {"transformed": export_log, "untransformed": raw_log}
            need(smts, f"Why3 exported no SMT goals for root {name}:{theory}.{goal}")
            leaf_records = []
            for leaf_i, smt in enumerate(smts):
                cmd = ["z3", "-smt2", f"-T:{args.time_limit}", "sat.random_seed=42",
                       "nlsat.randomize=false", "smt.random_seed=42", str(smt)]
                try:
                    solved = run(cmd, args.time_limit + 10)
                    stdout, stderr, exit_code = solved.stdout, solved.stderr, solved.returncode
                    statuses = [line.strip() for line in stdout.splitlines()
                                if line.strip() in {"sat", "unsat", "unknown", "timeout"}]
                except subprocess.TimeoutExpired as exc:
                    stdout = exc.stdout.decode(errors="replace") if isinstance(exc.stdout, bytes) else (exc.stdout or "")
                    stderr = exc.stderr.decode(errors="replace") if isinstance(exc.stderr, bytes) else (exc.stderr or "")
                    exit_code, statuses = None, ["timeout"]
                leaf_dir = root_dir / "solver" / f"{leaf_i:04d}-{smt.stem}"
                leaf_dir.mkdir(parents=True)
                (leaf_dir / "command.json").write_text(json.dumps(cmd, indent=2) + "\n")
                (leaf_dir / "stdout.txt").write_text(stdout)
                (leaf_dir / "stderr.txt").write_text(stderr)
                leaf_key = smt.relative_to(out).as_posix()
                digest = sha(smt); smt_hashes[leaf_key] = digest
                passed = (exit_code == 0 and statuses == ["unsat"]
                          and "(error" not in stdout.lower() and "(error" not in stderr.lower())
                primary_status = statuses[0] if len(statuses) == 1 else "error"
                secondary = None
                final_solver = "z3"
                final_exit_code = exit_code
                fallback_allowed = primary_status in {"timeout", "unknown"}
                if not passed and fallback_allowed:
                    secondary_cmd = [cvc5, f"--tlimit={args.cvc5_time_limit_ms}", str(smt)]
                    try:
                        secondary_proc = run(secondary_cmd, args.cvc5_time_limit_ms / 1000 + 10)
                        secondary_stdout, secondary_stderr = secondary_proc.stdout, secondary_proc.stderr
                        secondary_exit = secondary_proc.returncode
                        secondary_statuses = [line.strip() for line in secondary_stdout.splitlines()
                            if line.strip() in {"sat", "unsat", "unknown", "timeout"}]
                    except subprocess.TimeoutExpired as exc:
                        secondary_stdout = exc.stdout.decode(errors="replace") if isinstance(exc.stdout, bytes) else (exc.stdout or "")
                        secondary_stderr = exc.stderr.decode(errors="replace") if isinstance(exc.stderr, bytes) else (exc.stderr or "")
                        secondary_exit, secondary_statuses = None, []
                    secondary_closed = (secondary_exit == 0 and secondary_statuses == ["unsat"]
                        and "(error" not in secondary_stdout.lower()
                        and "(error" not in secondary_stderr.lower())
                    secondary_dir = root_dir / "solver-cvc5" / f"{leaf_i:04d}-{smt.stem}"
                    secondary_dir.mkdir(parents=True)
                    secondary_logs = save_process(out, secondary_dir, "solver", secondary_cmd,
                        subprocess.CompletedProcess(secondary_cmd, secondary_exit or 0,
                                                    secondary_stdout, secondary_stderr))
                    secondary = {"name": "cvc5", "process": secondary_logs,
                        "status": secondary_statuses[0] if len(secondary_statuses) == 1 else "error",
                        "exit_code": secondary_exit, "closed_original_smt": secondary_closed}
                    if secondary_closed:
                        passed, final_solver, final_exit_code = True, "cvc5", secondary_exit
                if not passed:
                    unresolved.append({"target": name, "root": f"{theory}.{goal}",
                        "smt": leaf_key, "status": statuses[0] if len(statuses) == 1 else "error",
                        "exit_code": exit_code, "secondary_status": secondary["status"] if secondary else None})
                leaf_records.append({"path": leaf_key, "sha256": digest,
                    "solver_command": (leaf_dir / "command.json").relative_to(out).as_posix(),
                    "solver_command_sha256": sha(leaf_dir / "command.json"),
                    "solver_stdout": (leaf_dir / "stdout.txt").relative_to(out).as_posix(),
                    "solver_stdout_sha256": sha(leaf_dir / "stdout.txt"),
                    "solver_stderr": (leaf_dir / "stderr.txt").relative_to(out).as_posix(),
                    "solver_stderr_sha256": sha(leaf_dir / "stderr.txt"),
                    "primary_status": primary_status, "status": "unsat" if passed else primary_status,
                    "primary_exit_code": exit_code, "exit_code": final_exit_code, "final_solver": final_solver,
                    "secondary_solver": secondary})
            root_closed = bool(leaf_records) and all(x["status"] == "unsat" and x["exit_code"] == 0
                and ((x["final_solver"] == "z3" and x["primary_status"] == "unsat")
                     or (x["final_solver"] == "cvc5" and x["secondary_solver"] is not None
                         and x["secondary_solver"]["closed_original_smt"]))
                for x in leaf_records)
            if root_closed: target_closed += 1
            else: target_open.append(f"{theory}.{goal}")
            mapped.append({"root": f"{theory}.{goal}", "status": "closed" if root_closed else "open", "export_mode": export_mode,
                           "export_command": export_log, "leaf_count": len(leaf_records),
                           "leaves": leaf_records})
        selected_records[name] = {"coma_path": f"generated/{name}.coma",
            "coma_origin_path": str(coma), "coma_sha256": sha(coma),
            "root_listing": listlog, "root_count": len(roots),
            "roots": [f"{t}.{g}" for t, g in roots], "closed_root_goals": target_closed,
            "open_root_goals": target_open, "proofs": mapped}
        total_roots += len(roots)
        closed_roots += target_closed
    need(total_roots > 0 and smt_hashes, "no positive root-goal or SMT-leaf count")
    smt_text = "\n".join(safe.read_text(errors="replace") for safe in
                           (out / rel for rel in smt_hashes))
    need("encoded_array_model" in smt_text and "byte_model_subsequence" in smt_text,
         "emitted SMT contains no selected runtime dependency calls")
    after = fingerprint()
    need(before == after, "source, docs, scripts, model, or dependency inputs changed during proof")
    tools_after = tool_fingerprint()
    need(tools_before == tools_after, "tool binaries changed during proof")
    versions = {}
    for tool in ("cargo", "cargo-creusot", "why3", "z3", "cvc5"):
        path = shutil.which(tool)
        need(path is not None, f"tool missing: {tool}")
        versions[tool] = {"path": str(Path(path).resolve()), "sha256": sha(Path(path).resolve())}
        if tool == "cvc5":
            version = run([str(Path(path).resolve()), "--version"])
            need(version.returncode == 0 and version.stdout.splitlines(),
                 "cvc5 --version returned no version identity")
            versions[tool]["version_line"] = version.stdout.splitlines()[0]
    generated_items = {}
    for name, path in actual.items():
        staged = out / "generated" / f"{name}.coma"
        staged.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, staged)
        generated_items[name] = {"path": f"generated/{name}.coma", "origin_path": str(path),
            "sha256": sha(staged), "classification": ("selected" if name in selected
                else "expected-open" if name in opened else "excluded")}
    compile_log = run_dir / "compile.log"
    need(compile_log.is_file(), "compile log missing")
    for name in ("compile.log", "cargo-metadata.json", "differential.log", "inputs-before.json"):
        source = run_dir / name
        need(source.is_file(), f"missing fresh-run artifact: {name}")
        shutil.copyfile(source, out / name)
    native_dir = run_dir / "native-evidence"
    native_names = [
        "differential-run-full-scope.log",
        "fork-unit-all-features-full-scope.log",
        "fork-doc-all-features-full-scope.log",
        "fork-check-default-full-scope.log",
        "fork-check-bare-full-scope.log",
        "fork-check-alloc-full-scope.log",
        "upstream-unit-all-features-full-scope.log",
        "source-fingerprint.txt",
    ]
    need(native_dir.is_dir(), "full-scope native evidence directory missing")
    need({p.name for p in native_dir.iterdir() if p.is_file()} == set(native_names),
         "full-scope native evidence log inventory differs from required set")
    shutil.copytree(native_dir, out / "native-evidence")
    native_log_hashes = {name: sha(native_dir / name) for name in native_names}
    native_fingerprint = (native_dir / "source-fingerprint.txt").read_text().splitlines()
    need(bool(native_fingerprint) and native_fingerprint[0].startswith("RUN_ID="),
         "native source fingerprint run ID is missing")
    native_run_id = native_fingerprint[0].removeprefix("RUN_ID=")
    need(native_run_id.startswith("percent-encoding-2.3.2-full-scope-")
         and native_run_id != "percent-encoding-2.3.2-full-scope-",
         "native run ID is not a unique full-scope identifier")
    for name in native_names[:-1]:
        lines = (native_dir / name).read_text(errors="replace").splitlines()
        need(bool(lines) and lines[0] == f"RUN_ID={native_run_id}",
             f"native log run ID mismatch: {name}")
    native_summary = [json.loads(line) for line in
        (native_dir / native_names[0]).read_text(errors="replace").splitlines()
        if line.startswith("{")]
    need(len(native_summary) == 1 and native_summary[0].get("run_id") == native_run_id
         and native_summary[0].get("status") == "passed"
         and native_summary[0].get("invalid_owned_utf8_error_checks", 0) >= 6,
         "native differential summary lacks the required full-scope/strict UTF-8 checks")
    need(native_fingerprint and "BEFORE" in native_fingerprint and "AFTER" in native_fingerprint,
         "native before/after source fingerprint is missing")
    metadata = json.loads((out / "cargo-metadata.json").read_text())
    packages = metadata.get("packages", [])
    form_package = next((p for p in packages if p.get("name") == "form_urlencoded"
                         and p.get("version") == "1.2.2"), None)
    percent_package = next((p for p in packages if p.get("name") == "percent-encoding"
                            and p.get("version") == "2.3.2"
                            and str(p.get("source", "")).startswith("registry+")), None)
    need(form_package is not None and form_package.get("source") is None
         and Path(form_package["manifest_path"]).resolve() ==
             (FORM / "crate/Cargo.toml").resolve(),
         "Cargo metadata did not resolve the intended local form_urlencoded path dependency")
    need(percent_package is not None and percent_package.get("source", "").startswith("registry+"),
         "Cargo metadata did not keep the dependency's percent-encoding on the registry")
    package_by_id = {p["id"]: p for p in packages}
    form_node = next((node for node in metadata.get("resolve", {}).get("nodes", [])
                      if node.get("id") == form_package.get("id")), None)
    need(form_node is not None and any(
        dep.get("pkg") in package_by_id
        and package_by_id[dep["pkg"]].get("name") == "percent-encoding"
        and package_by_id[dep["pkg"]].get("source") == percent_package.get("source")
        for dep in form_node.get("deps", [])),
        "form_urlencoded's percent-encoding edge is not the registry dependency")
    passed = not unresolved and closed_roots == total_roots
    manifest = {"schema": "percent-direct-solver-evidence-v1" if passed else "percent-direct-solver-attempt-v1",
        "status": "passed" if passed else "incomplete",
        "mode": "socket-free-direct-why3-smt-z3-cvc5", "created_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "solver": "z3 primary; cvc5 secondary on non-UNSAT", "time_limit_seconds": args.time_limit,
        "cvc5_time_limit_ms": args.cvc5_time_limit_ms,
        "rustc_host": subprocess.check_output(["rustc", "-Vv"], text=True).strip(),
                    "inputs_sha256": before, "inputs_after_sha256": after,
        "snapshot_sha256": sha(before_path), "toolchain_sha256": tools_before, "tool_sha256": versions,
        "bundle_origin_path": str(out),
        "compile_log_sha256": sha(compile_log), "dependency_audit_sha256": sha(out / "dependency-audit.json"),
        "cargo_metadata_sha256": sha(out / "cargo-metadata.json"),
        "differential_log_sha256": sha(out / "differential.log"),
        "compile_cwd": str(VERSION / "crate"),
        "compile_command": ["cargo", "creusot", "--only=coma", "--span-mode", "off",
            "--output-dir", str(run_dir / "coma"), "--", "--locked", "--offline",
            "--target-dir", str(run_dir / "target")],
        "dependency_evidence": dependency_audit, "selected_targets": selected_records,
        "native_evidence": {"run_id": native_run_id, "logs_sha256": native_log_hashes,
            "source_fingerprint": "native-evidence/source-fingerprint.txt"},
        "selected_target_count": len(selected_records), "generated_target_count": len(generated_items),
        "generated_target_inventory": generated_items,
        "target_classification": {"selected": sorted(selected), "expected_open": sorted(opened), "excluded": sorted(excluded)},
        "original_root_goal_count": total_roots, "closed_root_goal_count": closed_roots,
        "open_root_goals": sorted(f"{t}.{r}" for t, record in selected_records.items()
                                   for r in record["open_root_goals"]),
        "unresolved_results": unresolved, "smt_inventory_sha256": smt_hashes,
        "application_trusted_assumptions": [],
        "dependency_calls": sorted(source_calls),
        "limitations": "Direct closure of fresh Creusot-generated SMT obligations for selected target-inventory entries only. Logical imports and standard-library contracts remain assumptions; this is not upstream equivalence and does not cover excluded targets."}
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({"status": manifest["status"], "selected_targets": len(selected_records),
        "generated_targets": len(generated_items), "root_goals": total_roots,
        "smt_leaves": len(smt_hashes)}, indent=2))


if __name__ == "__main__":
    try: main()
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, subprocess.SubprocessError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
