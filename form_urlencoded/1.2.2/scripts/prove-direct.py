#!/usr/bin/env python3
"""Export fresh Creusot Coma VCs and prove each leaf with a direct SMT solver."""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
VERSION = HERE.parent
REPO = VERSION.parent.parent
CONF = Path(os.environ.get("XDG_DATA_HOME", "/workspace/.local/share")) / "creusot/creusot_why3.conf"
LIB = Path(os.environ.get("XDG_DATA_HOME", "/workspace/.local/share")) / "creusot/share/why3find/packages/creusot"


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def load_helper():
    path = HERE / "check-proofs.py"
    spec = importlib.util.spec_from_file_location("check_proofs", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def fingerprint():
    helper = load_helper()
    files = set(helper.input_paths(VERSION))
    files.update(HERE / n for n in ("prove-direct.py", "verify-direct.sh", "audit-direct-evidence.py"))
    # Pin the active Why3 config, prover drivers, and installed logical models.
    files.add(CONF)
    xdg = Path(os.environ.get("XDG_DATA_HOME", "/workspace/.local/share"))
    for path in (LIB, xdg / "creusot/_opam/share/why3/drivers"):
        if path.is_dir():
            files.update(p for p in path.rglob("*") if p.is_file())
    return {str(p.relative_to(VERSION) if p.is_relative_to(VERSION) else p): sha(p)
            for p in sorted(files) if p.is_file()}


def tool_fingerprint():
    return load_helper().tool_hashes()


def run(command, *, timeout, cwd=VERSION):
    return subprocess.run(command, cwd=cwd, capture_output=True, text=True,
                          timeout=timeout, env=os.environ.copy())


def why3_base():
    return ["why3", "prove", "-C", str(CONF), "-L", str(LIB)]


def roots_for(coma, timeout):
    cmd = why3_base() + [str(coma)]
    result = run(cmd, timeout=timeout)
    theory = None
    roots = []
    for line in result.stdout.splitlines():
        m = re.match(r"^theory (\S+)$", line)
        if m:
            theory = m.group(1)
        m = re.match(r"^  goal (\S+)\s*:", line)
        if m:
            need(theory is not None, f"Goal without theory in {coma}")
            roots.append((theory, m.group(1)))
    return roots, cmd, result


def store_process(directory, label, cmd, result):
    command = directory / f"{label}.command.json"
    stdout = directory / f"{label}.stdout.txt"
    stderr = directory / f"{label}.stderr.txt"
    command.write_text(json.dumps(cmd, indent=2) + "\n")
    stdout.write_text(result.stdout)
    stderr.write_text(result.stderr)
    return {"command": command, "stdout": stdout, "stderr": stderr}


def logged_record(out, paths):
    return {key: {"path": path.relative_to(out).as_posix(), "sha256": sha(path)}
            for key, path in paths.items()}


def solver_result(solver, smt, timeout):
    if solver == "z3":
        cmd = ["z3", "-smt2", f"-T:{math.ceil(timeout)}", "sat.random_seed=42",
               "nlsat.randomize=false", "smt.random_seed=42", str(smt)]
    elif solver == "cvc5":
        cmd = ["cvc5", "--lang=smt2", "--tlimit", str(int(timeout * 1000)), str(smt)]
    else:
        cmd = ["cvc5", "--lang=smt2", "--tlimit", str(int(timeout * 1000)), str(smt)]
    try:
        result = run(cmd, timeout=timeout + 5)
        statuses = [line.strip() for line in result.stdout.splitlines()
                    if line.strip() in {"sat", "unsat", "unknown", "timeout"}]
        errors = "(error" in result.stdout.lower() or result.returncode != 0
        return cmd, result, statuses, not errors and statuses == ["unsat"]
    except subprocess.TimeoutExpired as exc:
        return cmd, exc, [], False


def ground_fallback_bytes(raw):
    """Remove selected labeled root-forall axioms, preserving all other bytes."""
    text = raw.decode("ascii")
    tokens = []
    i = 0
    while i < len(text):
        c = text[i]
        if c.isspace():
            i += 1
        elif c == ';':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end + 1
        elif c in '()':
            tokens.append((c, i, i + 1)); i += 1
        elif c == '"':
            start = i; i += 1
            while i < len(text):
                if text[i] == '"':
                    if i + 1 < len(text) and text[i + 1] == '"': i += 2; continue
                    i += 1; break
                i += 1
            else: raise ValueError("unterminated SMT-LIB string")
            tokens.append(("<string>", start, i))
        elif c == '|':
            start = i; i += 1
            while i < len(text) and text[i] != '|': i += 1
            if i == len(text): raise ValueError("unterminated quoted SMT-LIB symbol")
            i += 1; tokens.append(("<quoted-symbol>", start, i))
        else:
            start = i
            while i < len(text) and not text[i].isspace() and text[i] not in '();': i += 1
            tokens.append((text[start:i], start, i))

    pos = 0
    def parse():
        nonlocal pos
        if pos >= len(tokens): raise ValueError("unexpected end of SMT-LIB")
        value, start, end = tokens[pos]; pos += 1
        if value != '(': return (value, start, end, None)
        children = []
        while pos < len(tokens) and tokens[pos][0] != ')': children.append(parse())
        if pos >= len(tokens): raise ValueError("unclosed SMT-LIB expression")
        _, _, end = tokens[pos]; pos += 1
        return (None, start, end, children)
    commands = []
    while pos < len(tokens): commands.append(parse())
    if not commands: raise ValueError("empty SMT-LIB document")
    def atom(node): return node[3][0][0] if node[3] else node[0]
    label_re = re.compile(r"^(?:infix =='spec(?:'0)?|map_u8_spec(?:'[0-9]+)?|byte_sequence_as_ints'def|t'int_closure_def|mixfix \[\.\.\]'spec(?:'0)?|percent_decoded_from_step_spec(?:'0)?|length_spec|t'axiom|extensionality|string_chunk_bytes'def|singleton'spec(?:'0)?|produces_ParseIntoOwned'def|owned_pair_singleton_spec(?:'0)?|cow_str_scalars'def|parse_suffix_after_next'def)$")
    def retained(node, command_start):
        def polymorphic(n):
            children = n[3]
            if not children:
                return False
            if atom(children[0]) == "forall":
                binders = children[1][3]
                if any(b[3] and b[3][1][0] == "ty" for b in binders):
                    return True
            return any(polymorphic(child) for child in children)
        labels = list(re.finditer(r'^;; "([^"\n]+)"\s*$', text[:command_start], re.M))
        label = labels[-1].group(1) if labels else ""
        return bool(label_re.fullmatch(label)) and not polymorphic(node)
    heads = [atom(c[3][0]) if c[3] else None for c in commands]
    assert_indices = [i for i, h in enumerate(heads) if h == "assert"]
    checks = [i for i, h in enumerate(heads) if h == "check-sat"]
    if len(assert_indices) < 1 or len(checks) != 1 or checks[0] != len(commands) - 1:
        raise ValueError("expected assertions followed by exactly one final check-sat")
    goal_i = assert_indices[-1]
    goal = commands[goal_i]
    if goal_i != checks[0] - 1 or len(goal[3]) != 2:
        raise ValueError("goal assertion is not the final command before check-sat")
    formula = goal[3][1]
    if not formula[3] or atom(formula[3][0]) != "not":
        raise ValueError("final assertion is not a negated goal")
    allowed = {"declare-sort", "declare-fun", "declare-const", "declare-datatypes",
               "define-sort", "define-fun", "define-funs-rec", "assert", "check-sat",
               "set-logic", "set-option", "set-info", "set-produce-models", "exit"}
    if any(h not in allowed for h in heads): raise ValueError("unsupported top-level SMT-LIB command")
    remove = []
    removed_sha = []
    for index in assert_indices[:-1]:
        command = commands[index]
        if len(command[3]) != 2: raise ValueError("malformed assert command")
        formula = command[3][1]
        if formula[3] and atom(formula[3][0]) == "forall" and not retained(formula, command[1]):
            remove.append((command[1], command[2]))
            removed_sha.append(hashlib.sha256(text[command[1]:command[2]].encode()).hexdigest())
    if not remove: raise ValueError("no quantified assumptions available for fallback")
    reduced = text
    for start, end in reversed(remove): reduced = reduced[:start] + reduced[end:]
    # Reparse to ensure a single unchanged final goal and check-sat remain.
    return reduced.encode("ascii"), removed_sha, len(remove)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--snapshot", type=Path, help="write a pre-compile direct input snapshot and exit")
    ap.add_argument("--generated-dir", type=Path,
                    help="fresh Coma root, e.g. RUN/coma/verif/form_urlencoded_rlib")
    ap.add_argument("--target", action="append", help="selected target (repeatable; default: all selected)")
    ap.add_argument("--solver", choices=("z3", "cvc5"), default="z3")
    ap.add_argument("--time-limit", type=float, default=30.0)
    ap.add_argument("--output", type=Path)
    ap.add_argument("--diagnostic", action="store_true",
                    help="prove existing Coma only; source freshness remains unverified")
    ap.add_argument("--inputs-before", type=Path,
                    help="pre-compile snapshot made by check-proofs.py --snapshot")
    ap.add_argument("--fresh-compile-assertion", action="store_true",
                    help="caller performed a clean offline compile after the snapshot")
    ap.add_argument("--require-complete-generated", action="store_true",
                    help="require selected and excluded Coma targets to match inventory")
    ap.add_argument("--keep-going", action="store_true",
                    help="attempt every fresh selected root; unresolved results produce attempt-report.json, never a passed manifest")
    ap.add_argument("--ground-fallback", action="store_true",
                    help="on original unknown/timeout only, try an audited query with universal assumptions removed")
    args = ap.parse_args()
    if args.snapshot:
        hashes = fingerprint()
        args.snapshot.write_text(json.dumps({"created_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
                                            "inputs_sha256": hashes,
                                            "tools_sha256": tool_fingerprint()}, indent=2) + "\n")
        print(f"Snapshotted {len(hashes)} direct verification inputs.")
        return
    need(args.time_limit > 0, "time limit must be positive")
    need(args.diagnostic or (args.inputs_before and args.fresh_compile_assertion),
         "fresh evidence requires --inputs-before and --fresh-compile-assertion; use --diagnostic for existing Coma")
    need(not (args.diagnostic and args.fresh_compile_assertion),
         "diagnostic mode cannot claim a fresh compile")
    need(args.generated_dir is not None and args.output is not None,
         "--generated-dir and --output are required for proof runs")
    generated = args.generated_dir.resolve()
    need(generated.is_dir(), f"fresh Coma directory missing: {generated}")
    inventory = json.loads((VERSION / "verification/target-inventory.json").read_text())
    selected = inventory["selected"]
    targets = args.target or list(selected)
    need(targets and len(set(targets)) == len(targets), "target list must be nonempty and unique")
    need(set(targets) <= set(selected), f"targets must be selected inventory entries: {sorted(set(targets)-set(selected))}")
    if args.fresh_compile_assertion:
        need(set(targets) == set(selected),
             "a fresh final direct bundle must attempt every selected target; use --diagnostic for a subset")
        need(args.require_complete_generated,
             "a fresh final direct bundle must check complete generated-target classification")
    if args.keep_going:
        need(args.fresh_compile_assertion and args.require_complete_generated and set(targets) == set(selected),
             "--keep-going is reserved for a full fresh selected-inventory attempt")
    out = args.output.resolve()
    need(not out.exists(), f"output directory already exists: {out}")
    out.mkdir(parents=True)
    inputs_before = fingerprint()
    tools_before = tool_fingerprint()
    if args.inputs_before:
        baseline_record = json.loads(args.inputs_before.read_text())
        baseline = baseline_record.get("inputs_sha256", {})
        need(baseline == inputs_before, "pre-compile snapshot differs from current direct-proof inputs")
        need(baseline_record.get("tools_sha256") == tools_before,
             "pre-compile tool hashes differ from current tool binaries")
    if args.require_complete_generated:
        need(not inventory.get("expected_open", {}),
             "direct complete-inventory mode does not support expected-open generated targets")
        expected = set(inventory["selected"]) | set(inventory["excluded_generated"])
        actual = {p.relative_to(generated).as_posix().removesuffix(".coma")
                  for p in generated.rglob("*.coma")}
        need(actual == expected,
             f"complete generated Coma inventory mismatch: missing={sorted(expected-actual)}, extra={sorted(actual-expected)}")
    generated_inventory = {}
    expected_open_names = set(inventory.get("expected_open", {}))
    for path in sorted(generated.rglob("*.coma")):
        name = path.relative_to(generated).as_posix().removesuffix(".coma")
        if name in selected:
            category = "selected"
        elif name in expected_open_names:
            category = "expected-open"
        elif name in inventory["excluded_generated"]:
            category = "excluded"
        else:
            category = "unclassified"
        generated_inventory[name] = {"path": str(path), "sha256": sha(path),
                                     "classification": category}
    records = {}
    unresolved = []
    try:
        for target in targets:
            coma = generated / f"{target}.coma"
            if not coma.is_file() and (generated / target / "target.coma").is_file():
                coma = generated / target / "target.coma"
            need(coma.is_file(), f"missing fresh Coma target: {coma}")
            target_dir = out / "targets" / target
            target_dir.mkdir(parents=True)
            original_roots, list_cmd, listed = roots_for(coma, args.time_limit + 30)
            original_log = logged_record(out, store_process(target_dir, "original-roots", list_cmd, listed))
            if listed.returncode != 0 or not original_roots or len(set(original_roots)) != len(original_roots):
                message = (f"Why3 root listing failed or returned an empty/duplicate root inventory "
                           f"(exit={listed.returncode}, roots={len(original_roots)})")
                if not args.keep_going:
                    need(False, f"{message}: {target}")
                records[target] = {"coma": str(coma), "coma_sha256": sha(coma),
                                   "original_roots": [f"{t}.{g}" for t, g in original_roots],
                                   "why3_root_listing": original_log,
                                   "why3_root_listing_exit_code": listed.returncode, "roots": [],
                                   "root_count": len(original_roots), "closed_root_goals": 0,
                                   "open_root_goals": [f"{t}.{g}" for t, g in original_roots],
                                   "target_error": message}
                unresolved.append({"target": target, "status": "root-listing-error", "detail": message})
                continue
            mapping = []
            for index, (theory, goal) in enumerate(original_roots):
                root_id = f"{index:04d}-{theory}-{goal}"
                root_dir = target_dir / "roots" / root_id
                root_dir.mkdir(parents=True)
                transformed_dir = root_dir / "transformed-export"
                baseline_dir = root_dir / "untransformed-export"
                transformed_dir.mkdir(parents=True)
                base = why3_base() + [str(coma), "-T", theory, "-G", goal]
                tx_cmd = base + ["-a", "compute_specified", "-a", "split_vc",
                                 "-P", "Z3", "-o", str(transformed_dir)]
                tx_result = run(tx_cmd, timeout=args.time_limit + 30)
                tx_log = logged_record(out, store_process(root_dir, "transformed-export", tx_cmd, tx_result))
                if tx_result.returncode != 0:
                    detail = f"transformed export failed (exit={tx_result.returncode})"
                    if not args.keep_going:
                        need(False, f"{detail} at {target}:{theory}.{goal}: {tx_result.stderr}")
                    mapping.append({"root": f"{theory}.{goal}", "status": "export-error",
                                    "detail": detail, "export_mode": "transformed",
                                    "transformed_exit_code": tx_result.returncode,
                                    "transformed_leaf_count": 0, "transformed_export": tx_log,
                                    "closure_export": None, "leaves": []})
                    unresolved.append({"target": target, "root": f"{theory}.{goal}",
                                       "status": "export-error", "detail": detail})
                    continue
                smt_files = sorted(transformed_dir.rglob("*.smt2"))
                mode = "transformed"
                fallback_log = None
                if not smt_files:
                    # A transformed empty result is accepted only when the independent
                    # no-transform export exposes the original root for direct solving.
                    baseline_dir.mkdir(parents=True)
                    raw_cmd = base + ["-P", "Z3", "-o", str(baseline_dir)]
                    raw_result = run(raw_cmd, timeout=args.time_limit + 30)
                    fallback_log = logged_record(out, store_process(root_dir, "untransformed-export", raw_cmd, raw_result))
                    if raw_result.returncode != 0:
                        detail = f"untransformed closure export failed (exit={raw_result.returncode})"
                        if not args.keep_going:
                            need(False, f"{detail} at {target}:{theory}.{goal}")
                        mapping.append({"root": f"{theory}.{goal}", "status": "export-error",
                                        "detail": detail, "export_mode": "untransformed-fallback",
                                        "transformed_exit_code": tx_result.returncode,
                                        "closure_exit_code": raw_result.returncode,
                                        "transformed_leaf_count": 0, "transformed_export": tx_log,
                                        "closure_export": fallback_log, "leaves": []})
                        unresolved.append({"target": target, "root": f"{theory}.{goal}",
                                           "status": "export-error", "detail": detail})
                        continue
                    smt_files = sorted(baseline_dir.rglob("*.smt2"))
                    if not smt_files:
                        detail = "zero transformed leaves and no independent original export"
                        if not args.keep_going:
                            need(False, f"{detail} at {target}:{theory}.{goal}")
                        mapping.append({"root": f"{theory}.{goal}", "status": "empty-export",
                                        "detail": detail, "export_mode": "untransformed-fallback",
                                        "transformed_exit_code": tx_result.returncode,
                                        "closure_exit_code": raw_result.returncode,
                                        "transformed_leaf_count": 0, "transformed_export": tx_log,
                                        "closure_export": fallback_log, "leaves": []})
                        unresolved.append({"target": target, "root": f"{theory}.{goal}",
                                           "status": "empty-export", "detail": detail})
                        continue
                    mode = "untransformed-fallback"
                leaf_items = []
                root_closed = True
                for leaf_index, smt in enumerate(smt_files):
                    solver_cmd, solver, status_lines, passed = solver_result(args.solver, smt, args.time_limit)
                    leaf_dir = root_dir / "solver" / f"{leaf_index:04d}-{smt.stem}"
                    leaf_dir.mkdir(parents=True)
                    (leaf_dir / "command.json").write_text(json.dumps(solver_cmd, indent=2) + "\n")
                    if isinstance(solver, subprocess.TimeoutExpired):
                        (leaf_dir / "stdout.txt").write_text(str(solver.stdout or ""))
                        (leaf_dir / "stderr.txt").write_text(str(solver.stderr or ""))
                        returncode = None
                    else:
                        (leaf_dir / "stdout.txt").write_text(solver.stdout)
                        (leaf_dir / "stderr.txt").write_text(solver.stderr)
                        returncode = solver.returncode
                    leaf_status = ("timeout" if isinstance(solver, subprocess.TimeoutExpired)
                                   else status_lines[0] if len(status_lines) == 1 else "error")
                    if not isinstance(solver, subprocess.TimeoutExpired) and solver.returncode != 0:
                        leaf_status = "error"
                    if not passed and leaf_status == "unsat":
                        leaf_status = "error"
                    fallback = None
                    closure_passed = passed
                    if args.ground_fallback and not passed and leaf_status in {"timeout", "unknown"}:
                        fallback_dir = leaf_dir / "ground-fallback"
                        fallback_dir.mkdir()
                        try:
                            reduced_bytes, removed_hashes, removed_count = ground_fallback_bytes(smt.read_bytes())
                            reduced_smt = fallback_dir / "reduced.smt2"
                            reduced_smt.write_bytes(reduced_bytes)
                            fcmd, fres, fstatuses, fpassed = solver_result(args.solver, reduced_smt, args.time_limit)
                            (fallback_dir / "command.json").write_text(json.dumps(fcmd, indent=2) + "\n")
                            if isinstance(fres, subprocess.TimeoutExpired):
                                (fallback_dir / "stdout.txt").write_text(str(fres.stdout or ""))
                                (fallback_dir / "stderr.txt").write_text(str(fres.stderr or ""))
                                fexit = None; fstatus = "timeout"
                            else:
                                (fallback_dir / "stdout.txt").write_text(fres.stdout)
                                (fallback_dir / "stderr.txt").write_text(fres.stderr)
                                fexit = fres.returncode
                                fstatus = fstatuses[0] if len(fstatuses) == 1 else "error"
                                if fres.returncode != 0:
                                    fstatus = "error"
                            fallback = {"method": "selected-original-assumptions-v1",
                                        "closure_method": "weakened-assumptions-unsat" if fpassed else None,
                                        "status": fstatus, "exit_code": fexit,
                                        "reduced_path": reduced_smt.relative_to(out).as_posix(),
                                        "reduced_sha256": sha(reduced_smt),
                                        "removed_assertion_count": removed_count,
                                        "removed_assertion_sha256": removed_hashes,
                                        "solver_command": (fallback_dir / "command.json").relative_to(out).as_posix(),
                                        "solver_command_sha256": sha(fallback_dir / "command.json"),
                                        "solver_stdout": (fallback_dir / "stdout.txt").relative_to(out).as_posix(),
                                        "solver_stdout_sha256": sha(fallback_dir / "stdout.txt"),
                                        "solver_stderr": (fallback_dir / "stderr.txt").relative_to(out).as_posix(),
                                        "solver_stderr_sha256": sha(fallback_dir / "stderr.txt")}
                            closure_passed = fpassed
                        except (ValueError, UnicodeError) as exc:
                            fallback = {"method": "selected-original-assumptions-v1",
                                        "status": "reduction-error", "detail": str(exc)}
                    leaf_item = {"path": smt.relative_to(out).as_posix(), "sha256": sha(smt),
                                       "solver_command": (leaf_dir / "command.json").relative_to(out).as_posix(),
                                       "solver_command_sha256": sha(leaf_dir / "command.json"),
                                       "solver_stdout": (leaf_dir / "stdout.txt").relative_to(out).as_posix(),
                                       "solver_stdout_sha256": sha(leaf_dir / "stdout.txt"),
                                       "solver_stderr": (leaf_dir / "stderr.txt").relative_to(out).as_posix(),
                                       "solver_stderr_sha256": sha(leaf_dir / "stderr.txt"),
                                       "status": leaf_status, "exit_code": returncode,
                                       "closure_status": "unsat" if closure_passed else leaf_status,
                                       "closure_method": ("original-smt-unsat" if passed else
                                                          fallback.get("closure_method") if fallback else None),
                                       "ground_fallback": fallback}
                    leaf_items.append(leaf_item)
                    if not closure_passed:
                        root_closed = False
                        if not args.keep_going:
                            need(False, f"solver did not return exactly unsat (status={status_lines}, exit={returncode}) for {target}:{theory}.{goal}:{smt.name}")
                        unresolved.append({"target": target, "root": f"{theory}.{goal}",
                                           "leaf": smt.relative_to(out).as_posix(),
                                           "status": leaf_status, "solver_exit_code": returncode})
                if not leaf_items:
                    root_closed = False
                mapping.append({"root": f"{theory}.{goal}",
                                "status": "closed" if root_closed else "open",
                                "export_mode": mode,
                                "transformed_exit_code": tx_result.returncode,
                                "closure_exit_code": (raw_result.returncode if mode == "untransformed-fallback" else None),
                                "transformed_leaf_count": len(sorted(transformed_dir.rglob("*.smt2"))),
                                "transformed_export": tx_log, "closure_export": fallback_log,
                                "leaves": leaf_items})
                if not root_closed and not any(item.get("target") == target and item.get("root") == f"{theory}.{goal}"
                                               for item in unresolved):
                    unresolved.append({"target": target, "root": f"{theory}.{goal}",
                                       "status": "empty-leaf-set"})
            closed_roots = sum(1 for root in mapping if root.get("status") == "closed")
            open_roots = [root["root"] for root in mapping if root.get("status") != "closed"]
            records[target] = {"coma": str(coma), "coma_sha256": sha(coma),
                               "original_roots": [f"{t}.{g}" for t, g in original_roots],
                               "why3_root_listing": original_log,
                               "why3_root_listing_exit_code": listed.returncode,
                               "roots": mapping, "root_count": len(original_roots),
                               "closed_root_goals": closed_roots,
                               "open_root_goals": open_roots}
        inputs_after = fingerprint()
        input_changes = sorted(name for name in set(inputs_before) | set(inputs_after)
                               if inputs_before.get(name) != inputs_after.get(name))
        need(not input_changes or args.diagnostic,
             f"verification inputs changed while direct proof was running: {input_changes}")
        tools_after = tool_fingerprint()
        need(tools_before == tools_after, "verification tool binaries changed during direct proof")
        smt_inventory = {p.relative_to(out).as_posix(): sha(p) for p in sorted(out.rglob("*.smt2"))}
        need(bool(smt_inventory) or args.keep_going, "no SMT exports were generated")
        toolnames = ["why3", args.solver]
        tools = {}
        for name in toolnames:
            path = shutil.which(name)
            need(path, f"tool not found: {name}")
            tools[name] = {"path": str(Path(path).resolve()), "sha256": sha(path)}
        model_inputs = sorted(name for name in inputs_before
                              if "creusot-std-0.13.0" in name
                              or "/creusot/share/why3find/packages/creusot/" in name)
        selected_all_attempted = set(records) == set(selected)
        requested_targets_closed = (not unresolved
                                    and all(not record.get("open_root_goals") and not record.get("target_error")
                                            for record in records.values()))
        selected_all_closed = selected_all_attempted and requested_targets_closed
        overall_status = "passed" if requested_targets_closed else "incomplete"
        manifest = {"schema": "direct-solver-evidence-v1" if overall_status == "passed"
                    else "direct-solver-attempt-report-v1",
                    "status": overall_status,
                    "created_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
                    "mode": "socket-free-direct-solver", "solver": args.solver,
                    "bundle_origin_path": str(out),
                    "time_limit_seconds": args.time_limit, "why3_config": str(CONF),
                    "why3_library": str(LIB), "tools_sha256": tools,
                    "toolchain_sha256": tools_before,
                    "trusted_boundary": {
                        "application_trusted_assumptions": [],
                        "standard_library_contracts": [
                            "Creusot/creusot-std 0.13 models for integer, u8, slice, and mutable-slice operations used by translated goals.",
                            "Explicit extern_spec contracts in crate/src/stdlib_models.rs for str::as_bytes, slice::split_first/split_at, String::from_utf8_lossy, String::push_str/truncate, and core::str::from_utf8_unchecked validity.",
                        ],
                        "contract_ledger": "verification/assumptions.md",
                        "application_model_source": "crate/src/stdlib_models.rs",
                        "model_inputs_sha256_keys": model_inputs,
                        "limitation": "These contracts are logical assumptions supplied to Why3. Direct SMT closure does not validate Rust standard-library implementations or establish that the contracts match every runtime behavior.",
                    },
                    "rustc_host": subprocess.check_output(["rustc", "-Vv"], text=True).strip(),
                    "inputs_sha256": inputs_before, "inputs_after_sha256": inputs_after,
                    "source_inputs_changed_during_run": input_changes,
                    "selected_targets": records,
                    "selected_inventory_targets": sorted(selected),
                    "selected_inventory_target_count": len(selected),
                    "attempted_selected_targets": sorted(records),
                    "deferred_selected_targets": sorted(set(selected) - set(records)),
                    "selected_inventory_attempted_complete": selected_all_attempted,
                    "selected_proof_complete": selected_all_closed,
                    "proof_scope": ("complete-selected-inventory" if selected_all_attempted
                                    else "selected-target-subset"),
                    "expected_open_targets": sorted(inventory.get("expected_open", {})),
                    "excluded_generated_targets": sorted(inventory["excluded_generated"]),
                    "complete_generated_inventory_checked": args.require_complete_generated,
                    "generated_target_count": len(generated_inventory),
                    "generated_target_inventory": generated_inventory,
                    "current_source_freshness": bool(args.fresh_compile_assertion and not args.diagnostic),
                    "fresh_compile_command": "cargo +nightly-2026-06-22 clean --target-dir target/creusot -p form_urlencoded; cargo creusot --only=coma --span-mode off --output-dir RUN/coma -- --locked --offline" if args.fresh_compile_assertion else None,
                    "precompile_snapshot_sha256": sha(args.inputs_before) if args.inputs_before else None,
                    "selected_target_count": len(records),
                    "original_root_goal_count": sum(x["root_count"] for x in records.values()),
                    "closed_root_goal_count": sum(x["closed_root_goals"] for x in records.values()),
                    "open_root_goals": sorted(f"{target}.{root}" for target, item in records.items()
                                               for root in item.get("open_root_goals", [])),
                    "unresolved_results": unresolved,
                    "unresolved_result_count": len(unresolved),
                    "smt_inventory_sha256": smt_inventory,
                    "ground_fallback_enabled": args.ground_fallback,
                    "limitations": "Direct solver checks of emitted SMT tasks; selected-original-assumptions-v1 UNSAT is a separate weakened-assumptions closure method and is never reported as UNSAT for the original SMT input. The reduction removes only selected existing top-level root-forall assertions; retained labeled axioms and every non-root-forall assertion are preserved, including nested forall and exists forms. No Why3 saved-session proof.json is asserted. This does not prove upstream equivalence or excluded APIs."}
        output_name = "manifest.json" if overall_status == "passed" else "attempt-report.json"
        (out / output_name).write_text(json.dumps(manifest, indent=2) + "\n")
        print(json.dumps({"status": overall_status, "report": str(out / output_name),
                          "selected_targets": len(records),
                          "selected_inventory_targets": len(selected),
                          "deferred_selected_targets": len(set(selected) - set(records)),
                          "selected_inventory_attempted_complete": selected_all_attempted,
                          "selected_proof_complete": selected_all_closed,
                          "proof_scope": ("complete-selected-inventory" if selected_all_attempted
                                         else "selected-target-subset"),
                          "original_root_goals": manifest["original_root_goal_count"],
                          "closed_root_goals": manifest["closed_root_goal_count"],
                          "open_root_goals": len(manifest["open_root_goals"]),
                          "unresolved_results": len(unresolved),
                          "smt_leaves": len(smt_inventory)}, indent=2))
    except Exception:
        # Preserve a failure record, but never label the bundle successful.
        (out / "failure.txt").write_text("Direct proof failed; inspect target logs.\n")
        raise


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
