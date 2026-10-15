#!/usr/bin/env python3
"""Diagnostic-only direct Why3 export and Z3/CVC5 runner for explicit Coma targets.

This tool records what the supplied generated Coma proves. It does not fingerprint
Rust source, assert a fresh translation, classify whole-crate coverage, or emit a
passing evidence manifest.
"""
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

VERSION = Path(__file__).resolve().parent.parent
XDG = Path(os.environ.get("XDG_DATA_HOME", "/workspace/.local/share"))
CONF = XDG / "creusot/creusot_why3.conf"
LIB = XDG / "creusot/share/why3find/packages/creusot"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def store(directory, label, command, proc):
    directory.mkdir(parents=True, exist_ok=True)
    records = {}
    for suffix, data in (("command.json", json.dumps(command, indent=2) + "\n"),
                         ("stdout.txt", proc.stdout), ("stderr.txt", proc.stderr)):
        path = directory / f"{label}.{suffix}"
        path.write_text(data)
        records[suffix] = {"path": str(path), "sha256": sha(path)}
    return records


def invoke(command, timeout):
    return subprocess.run(command, cwd=VERSION, capture_output=True, text=True,
                          timeout=timeout, env=os.environ.copy())


def parse_roots(stdout):
    roots, theory = [], None
    for line in stdout.splitlines():
        match = re.match(r"^theory (\S+)$", line)
        if match: theory = match.group(1)
        match = re.match(r"^  goal (\S+)\s*:", line)
        if match and theory is not None: roots.append((theory, match.group(1)))
    return roots


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--generated-dir", type=Path, required=True,
                    help="root containing the supplied fresh .coma files")
    ap.add_argument("--target", action="append", required=True,
                    help="target path relative to --generated-dir, without .coma; repeatable")
    ap.add_argument("--output", type=Path, required=True,
                    help="new directory for this diagnostic's logs and report")
    ap.add_argument("--solver-time-limit", type=int, default=10)
    ap.add_argument("--cvc5-time-limit-ms", type=int, default=60_000)
    args = ap.parse_args()
    if args.solver_time_limit < 1: raise ValueError("solver time limit must be positive")
    if args.cvc5_time_limit_ms < 1: raise ValueError("cvc5 time limit must be positive")
    cvc5 = shutil.which("cvc5")
    if not cvc5: raise ValueError("cvc5 is required on activated PATH as the secondary solver")
    generated, output = args.generated_dir.resolve(), args.output.resolve()
    if not generated.is_dir(): raise ValueError(f"generated directory missing: {generated}")
    if output.exists(): raise ValueError(f"output already exists: {output}")
    if len(args.target) != len(set(args.target)): raise ValueError("duplicate target requested")
    comas = {}
    for name in args.target:
        relative = Path(name)
        if relative.is_absolute() or ".." in relative.parts or not relative.parts:
            raise ValueError(f"target must be a safe relative path: {name}")
        coma = (generated / f"{relative.as_posix()}.coma").resolve()
        if not coma.is_relative_to(generated):
            raise ValueError(f"target resolves outside generated Coma directory: {name}")
        if not coma.is_file(): raise ValueError(f"fresh Coma target is missing: {coma}")
        comas[name] = coma
    output.mkdir(parents=True)
    why3 = ["why3", "prove", "-C", str(CONF), "-L", str(LIB)]
    targets, unresolved = {}, []
    for name in args.target:
        relative = Path(name)
        coma = comas[name]
        target_dir = output / "targets" / relative
        root_cmd = why3 + [str(coma)]
        listing = invoke(root_cmd, timeout=120)
        listing_files = store(target_dir, "root-listing", root_cmd, listing)
        roots = parse_roots(listing.stdout)
        target_result = {"coma_path": str(coma), "coma_sha256": sha(coma),
                         "root_listing": listing_files, "root_listing_exit_code": listing.returncode,
                         "roots": [], "positive_root_count": len(roots)}
        if listing.returncode != 0 or not roots:
            unresolved.append({"target": name, "status": "root-listing-error",
                               "exit_code": listing.returncode, "root_count": len(roots)})
            targets[name] = target_result
            continue
        for index, (theory, goal) in enumerate(roots):
            root = target_dir / "roots" / f"{index:04d}-{theory}-{goal}"
            transformed = root / "transformed"
            transformed.mkdir(parents=True)
            base = why3 + [str(coma), "-T", theory, "-G", goal]
            tx_cmd = base + ["-a", "compute_specified", "-a", "split_vc",
                             "-P", "Z3", "-o", str(transformed)]
            tx = invoke(tx_cmd, timeout=120)
            tx_log = store(root, "transformed-export", tx_cmd, tx)
            root_result = {"root": f"{theory}.{goal}", "transformed_export": tx_log,
                           "transformed_exit_code": tx.returncode, "export_mode": "transformed",
                           "leaves": [], "status": "incomplete"}
            if tx.returncode != 0:
                root_result["export_error"] = "transformed export failed"
                unresolved.append({"target": name, "root": root_result["root"], "status": "export-error"})
                target_result["roots"].append(root_result)
                continue
            smts = sorted(transformed.rglob("*.smt2"))
            if not smts:
                original = root / "untransformed-original-root"
                original.mkdir()
                original_cmd = base + ["-P", "Z3", "-o", str(original)]
                original_proc = invoke(original_cmd, timeout=120)
                original_log = store(root, "untransformed-export", original_cmd, original_proc)
                root_result["untransformed_export"] = original_log
                root_result["untransformed_exit_code"] = original_proc.returncode
                root_result["export_mode"] = "untransformed-original-root"
                smts = sorted(original.rglob("*.smt2"))
                if original_proc.returncode != 0 or not smts:
                    root_result["export_error"] = "zero transformed leaves and no original root tasks"
                    unresolved.append({"target": name, "root": root_result["root"],
                                       "status": "empty-export"})
                    target_result["roots"].append(root_result)
                    continue
            root_closed = True
            for leaf_index, smt in enumerate(smts):
                command = ["z3", "-smt2", f"-T:{args.solver_time_limit}", "sat.random_seed=42",
                           "nlsat.randomize=false", "smt.random_seed=42", str(smt)]
                leaf_dir = root / "solver" / f"{leaf_index:04d}-{smt.stem}"
                try:
                    result = invoke(command, timeout=args.solver_time_limit + 10)
                    stdout, stderr, exit_code = result.stdout, result.stderr, result.returncode
                    statuses = [line.strip() for line in stdout.splitlines()
                                if line.strip() in {"sat", "unsat", "unknown", "timeout"}]
                except subprocess.TimeoutExpired as exc:
                    stdout = exc.stdout.decode(errors="replace") if isinstance(exc.stdout, bytes) else (exc.stdout or "")
                    stderr = exc.stderr.decode(errors="replace") if isinstance(exc.stderr, bytes) else (exc.stderr or "")
                    exit_code, statuses = None, ["timeout"]
                fake = subprocess.CompletedProcess(command, exit_code or 0, stdout, stderr)
                solver_logs = store(leaf_dir, "solver", command, fake)
                closed = (exit_code == 0 and statuses == ["unsat"]
                          and "(error" not in stdout.lower() and "(error" not in stderr.lower())
                primary_status = statuses[0] if len(statuses) == 1 else "error"
                secondary, final_solver = None, "z3"
                fallback_allowed = primary_status in {"timeout", "unknown"}
                if not closed and fallback_allowed:
                    secondary_cmd = [cvc5, f"--tlimit={args.cvc5_time_limit_ms}", str(smt)]
                    try:
                        secondary_proc = invoke(secondary_cmd, timeout=args.cvc5_time_limit_ms / 1000 + 10)
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
                    secondary_dir = leaf_dir / "cvc5"
                    secondary_logs = store(secondary_dir, "solver", secondary_cmd,
                        subprocess.CompletedProcess(secondary_cmd, secondary_exit or 0,
                                                    secondary_stdout, secondary_stderr))
                    secondary = {"name": "cvc5", "process": secondary_logs,
                        "status": secondary_statuses[0] if len(secondary_statuses) == 1 else "error",
                        "exit_code": secondary_exit, "closed_original_smt": secondary_closed}
                    if secondary_closed:
                        closed, final_solver = True, "cvc5"
                leaf = {"path": str(smt), "sha256": sha(smt), "solver": solver_logs,
                        "primary_status": primary_status,
                        "status": "unsat" if closed else primary_status,
                        "exit_code": exit_code, "final_solver": final_solver,
                        "secondary_solver": secondary, "closed_original_smt": closed}
                root_result["leaves"].append(leaf)
                if not closed:
                    root_closed = False
                    unresolved.append({"target": name, "root": root_result["root"],
                        "smt_path": str(smt), "status": leaf["status"], "exit_code": exit_code})
            root_result["status"] = "closed" if root_closed else "incomplete"
            target_result["roots"].append(root_result)
        targets[name] = target_result
    total_roots = sum(t["positive_root_count"] for t in targets.values())
    total_closed = sum(1 for t in targets.values() for r in t["roots"] if r["status"] == "closed")
    report = {"schema": "diagnostic-direct-solver-report-v1",
              "mode": "diagnostic-only; supplied generated Coma; no fresh-source claim",
              "created_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
              "generated_dir": str(generated), "targets": targets,
              "requested_targets": args.target, "positive_root_count": total_roots,
              "closed_root_count": total_closed, "unresolved": unresolved,
              "status": "diagnostic-complete" if not unresolved else "diagnostic-incomplete",
              "limitation": "No source snapshot, full generated-target classification, native test claim, or final evidence status is represented. Every root and original SMT leaf status must be reviewed separately."}
    (output / "diagnostic-report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "targets": len(targets),
                      "positive_roots": total_roots, "closed_roots": total_closed,
                      "unresolved": len(unresolved), "report": str(output / "diagnostic-report.json")}, indent=2))
    if unresolved: return 1
    return 0


if __name__ == "__main__":
    try: sys.exit(main())
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError,
            subprocess.SubprocessError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
