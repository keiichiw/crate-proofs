#!/usr/bin/env python3
"""Validate a direct SMT solver evidence bundle against its inputs and files."""
import argparse
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import sys


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def read(path):
    return json.loads(path.read_text(), object_pairs_hook=unique_pairs)


def unique_pairs(pairs):
    value = {}
    for k, v in pairs:
        require(k not in value, f"duplicate JSON key: {k}")
        value[k] = v
    return value


def helper(version):
    path = version / "scripts/check-proofs.py"
    spec = importlib.util.spec_from_file_location("check_proofs_audit", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def tool_hashes(version):
    return helper(version).tool_hashes()


def input_hashes(version):
    files = set(helper(version).input_paths(version))
    scripts = version / "scripts"
    files.update(scripts / n for n in ("prove-direct.py", "verify-direct.sh", "audit-direct-evidence.py"))
    xdg = Path(os.environ.get("XDG_DATA_HOME", "/workspace/.local/share"))
    config = xdg / "creusot/creusot_why3.conf"
    library = xdg / "creusot/share/why3find/packages/creusot"
    drivers = xdg / "creusot/_opam/share/why3/drivers"
    files.add(config)
    for tree in (library, drivers):
        if tree.is_dir():
            files.update(p for p in tree.rglob("*") if p.is_file())
    return {str(p.relative_to(version) if p.is_relative_to(version) else p): sha(p)
            for p in sorted(files) if p.is_file()}


def safe_rel(value):
    path = PurePosixPath(value)
    require(isinstance(value, str) and bool(value) and not path.is_absolute()
            and ".." not in path.parts and str(path) == value,
            f"unsafe relative path: {value}")
    return Path(*path.parts)


def check_log(base, record, label, expected_terms):
    require(isinstance(record, dict) and set(record) == {"command", "stdout", "stderr"},
            f"missing {label} process record")
    values = {}
    for key, item in record.items():
        path = base / safe_rel(item["path"])
        require(path.is_file() and sha(path) == item["sha256"], f"{label} {key} hash mismatch")
        values[key] = path
    command = read(values["command"])
    require(isinstance(command, list) and command and Path(command[0]).name == "why3",
            f"unexpected {label} command")
    for term in expected_terms:
        require(term in command, f"{label} command missing {term}")
    return command


def ground_fallback_bytes(raw):
    """Independently reconstruct selected labeled root-forall axiom removal."""
    text = raw.decode("ascii")
    tokens = []
    i = 0
    while i < len(text):
        c = text[i]
        if c.isspace(): i += 1
        elif c == ';':
            end = text.find('\n', i); i = len(text) if end < 0 else end + 1
        elif c in '()': tokens.append((c, i, i + 1)); i += 1
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
            if i == len(text): raise ValueError("unterminated quoted symbol")
            i += 1; tokens.append(("<quoted-symbol>", start, i))
        else:
            start = i
            while i < len(text) and not text[i].isspace() and text[i] not in '();': i += 1
            tokens.append((text[start:i], start, i))
    pos = 0
    def parse():
        nonlocal pos
        if pos >= len(tokens): raise ValueError("unexpected end")
        value, start, end = tokens[pos]; pos += 1
        if value != '(': return (value, start, end, None)
        children = []
        while pos < len(tokens) and tokens[pos][0] != ')': children.append(parse())
        if pos >= len(tokens): raise ValueError("unclosed expression")
        _, _, end = tokens[pos]; pos += 1
        return (None, start, end, children)
    commands = []
    while pos < len(tokens): commands.append(parse())
    def head(node): return node[3][0][0] if node[3] else node[0]
    label_re = re.compile(r"^(?:infix =='spec(?:'0)?|map_u8_spec(?:'[0-9]+)?|byte_sequence_as_ints'def|t'int_closure_def|mixfix \[\.\.\]'spec(?:'0)?|percent_decoded_from_step_spec(?:'0)?|length_spec|t'axiom|extensionality|string_chunk_bytes'def|singleton'spec(?:'0)?|produces_ParseIntoOwned'def|owned_pair_singleton_spec(?:'0)?|cow_str_scalars'def|parse_suffix_after_next'def)$")
    def retained(node, command_start):
        def polymorphic(n):
            children = n[3]
            if not children:
                return False
            if head(children[0]) == "forall":
                binders = children[1][3]
                if any(b[3] and b[3][1][0] == "ty" for b in binders):
                    return True
            return any(polymorphic(child) for child in children)
        labels = list(re.finditer(r'^;; "([^"\n]+)"\s*$', text[:command_start], re.M))
        label = labels[-1].group(1) if labels else ""
        return bool(label_re.fullmatch(label)) and not polymorphic(node)
    heads = [head(node) for node in commands]
    indexes = [i for i, value in enumerate(heads) if value == "assert"]
    checks = [i for i, value in enumerate(heads) if value == "check-sat"]
    require(indexes and len(checks) == 1 and checks[0] == len(commands) - 1,
            "fallback source lacks one final check-sat")
    goal_index = indexes[-1]
    goal = commands[goal_index]
    require(goal_index == checks[0] - 1 and len(goal[3]) == 2
            and goal[3][1][3] and head(goal[3][1]) == "not",
            "fallback source final assertion is not a negated goal")
    allowed = {"declare-sort", "declare-fun", "declare-const", "declare-datatypes",
               "define-sort", "define-fun", "define-funs-rec", "assert", "check-sat",
               "set-logic", "set-option", "set-info", "set-produce-models", "exit"}
    require(all(value in allowed for value in heads), "fallback source has unsupported SMT-LIB command")
    removed = []
    for index in indexes[:-1]:
        command = commands[index]
        require(len(command[3]) == 2, "malformed source assert")
        formula = command[3][1]
        if formula[3] and head(formula) == "forall" and not retained(formula, command[1]):
            removed.append((command[1], command[2],
                            hashlib.sha256(text[command[1]:command[2]].encode()).hexdigest()))
    require(removed, "fallback source has no quantified assumptions")
    reduced = text
    for start, end, _ in reversed(removed): reduced = reduced[:start] + reduced[end:]
    return reduced.encode("ascii"), [digest for _, _, digest in removed], len(removed)


def audit_ground_fallback(base, leaf, solver_name, timeout, bundle_origin=None):
    fallback = leaf.get("ground_fallback")
    if fallback is None:
        require(leaf.get("closure_method") == "original-smt-unsat"
                and leaf.get("status") == "unsat" and leaf.get("closure_status") == "unsat",
                f"leaf lacks valid closure provenance: {leaf.get('path')}")
        return None
    require(leaf.get("status") in {"timeout", "unknown"},
            "fallback may only follow an original timeout/unknown")
    require(fallback.get("method") == "selected-original-assumptions-v1",
            "unknown fallback reduction method")
    if fallback.get("status") == "reduction-error":
        require(leaf.get("closure_status") == leaf.get("status")
                and leaf.get("closure_method") is None, "invalid failed fallback record")
        return None
    expected, hashes, count = ground_fallback_bytes((base / safe_rel(leaf["path"])).read_bytes())
    reduced_rel = safe_rel(fallback["reduced_path"])
    reduced = base / reduced_rel
    require(reduced.is_file() and reduced.read_bytes() == expected
            and sha(reduced) == fallback.get("reduced_sha256"),
            "fallback SMT does not match deterministic assumption reduction")
    require(fallback.get("removed_assertion_count") == count
            and fallback.get("removed_assertion_sha256") == hashes,
            "fallback removed-assertion inventory mismatch")
    for key, hash_key in (("solver_command", "solver_command_sha256"),
                          ("solver_stdout", "solver_stdout_sha256"),
                          ("solver_stderr", "solver_stderr_sha256")):
        path = base / safe_rel(fallback[key])
        require(path.is_file() and sha(path) == fallback.get(hash_key),
                f"fallback solver artifact hash mismatch: {path}")
    command = read(base / safe_rel(fallback["solver_command"]))
    origin = Path(bundle_origin).resolve() if bundle_origin is not None else base.resolve()
    require(origin.is_absolute(), "fallback bundle origin must be absolute")
    solver_input = origin / reduced_rel
    if solver_name == "z3":
        expected_command = ["z3", "-smt2", f"-T:{math.ceil(timeout)}", "sat.random_seed=42",
                            "nlsat.randomize=false", "smt.random_seed=42", str(solver_input)]
    else:
        expected_command = ["cvc5", "--lang=smt2", "--tlimit", str(int(timeout * 1000)), str(solver_input)]
    require(command == expected_command, "fallback solver command is not the configured direct invocation")
    stdout = (base / safe_rel(fallback["solver_stdout"])).read_text()
    stderr = (base / safe_rel(fallback["solver_stderr"])).read_text()
    statuses = [line.strip() for line in stdout.splitlines()
                if line.strip() in {"sat", "unsat", "unknown", "timeout"}]
    state = fallback.get("status")
    if state in {"unsat", "sat", "unknown"}:
        require(statuses == [state] and fallback.get("exit_code") == 0
                and "(error" not in stdout.lower() and "(error" not in stderr.lower(),
                "fallback solver status/output mismatch")
    elif state == "timeout":
        require(fallback.get("exit_code") is None or
                (solver_name == "z3" and fallback.get("exit_code") == 0 and statuses == ["timeout"]),
                "fallback timeout has inconsistent solver output")
    else:
        require(state == "error" and (fallback.get("exit_code") not in (None, 0)
                or len(statuses) != 1 or "(error" in stdout.lower()),
                "fallback error status/output mismatch")
    passed = (fallback.get("status") == "unsat" and fallback.get("exit_code") == 0
              and statuses == ["unsat"] and "(error" not in stdout.lower())
    if passed:
        require(fallback.get("closure_method") == "weakened-assumptions-unsat"
                and leaf.get("closure_method") == "weakened-assumptions-unsat"
                and leaf.get("closure_status") == "unsat",
                "fallback UNSAT is not labeled as weakened-assumptions closure")
    else:
        require(fallback.get("closure_method") is None
                and leaf.get("closure_status") == leaf.get("status"),
                "failed fallback falsely claims closure")
    return reduced_rel


def audit_attempt(version, manifest_path, data):
    """Audit an explicitly incomplete full-inventory attempt report."""
    base = manifest_path.parent
    require(data.get("schema") == "direct-solver-attempt-report-v1"
            and data.get("status") == "incomplete"
            and data.get("mode") == "socket-free-direct-solver",
            "attempt report must use the incomplete report schema/status")
    require(type(data.get("ground_fallback_enabled")) is bool,
            "attempt report lacks explicit ground-fallback setting")
    require(data.get("current_source_freshness") is True,
            "full attempt report must be tied to a fresh-source run")
    before = data.get("inputs_sha256")
    after = data.get("inputs_after_sha256")
    require(isinstance(before, dict) and isinstance(after, dict) and before == after,
            "full attempt source inputs changed during the run")
    require(input_hashes(version) == after, "attempt report input fingerprints do not match current files")
    require(data.get("source_inputs_changed_during_run") == [], "attempt report records changed source inputs")
    require(data.get("toolchain_sha256") == tool_hashes(version), "attempt report toolchain hash mismatch")
    boundary = data.get("trusted_boundary")
    require(isinstance(boundary, dict) and boundary.get("application_trusted_assumptions") == []
            and boundary.get("contract_ledger") == "verification/assumptions.md"
            and boundary.get("application_model_source") == "crate/src/stdlib_models.rs",
            "attempt report trusted-boundary record is incomplete")
    model_keys = sorted(name for name in before
                        if "creusot-std-0.13.0" in name
                        or "/creusot/share/why3find/packages/creusot/" in name)
    require(boundary.get("model_inputs_sha256_keys") == model_keys
            and "crate/src/stdlib_models.rs" in before
            and "verification/assumptions.md" in before,
            "attempt report did not fingerprint the declared model boundary")

    inventory = read(version / "verification/target-inventory.json")
    selected = sorted(inventory["selected"])
    targets = data.get("selected_targets")
    require(isinstance(targets, dict) and sorted(targets) == selected,
            "attempt report must account for every selected target")
    require(data.get("selected_inventory_targets") == selected
            and data.get("attempted_selected_targets") == selected
            and data.get("deferred_selected_targets") == [],
            "attempt report selected-target accounting is incomplete")
    require(data.get("selected_inventory_attempted_complete") is True
            and data.get("selected_proof_complete") is False
            and data.get("proof_scope") == "complete-selected-inventory",
            "attempt report completeness labels are inconsistent")
    expected_open = set(inventory.get("expected_open", {}))
    excluded = set(inventory["excluded_generated"])
    generated = data.get("generated_target_inventory")
    require(isinstance(generated, dict)
            and data.get("complete_generated_inventory_checked") is True
            and set(generated) == set(selected) | expected_open | excluded,
            "attempt report generated-target inventory is incomplete")
    require(data.get("generated_target_count") == len(generated), "generated target count mismatch")
    for name, item in generated.items():
        category = ("selected" if name in selected else
                    "expected-open" if name in expected_open else "excluded")
        path = Path(item.get("path", ""))
        require(item.get("classification") == category and path.is_file()
                and sha(path) == item.get("sha256"), f"generated Coma mismatch: {name}")

    solver_name = data.get("solver")
    require(solver_name in {"z3", "cvc5"}, "unknown solver in attempt report")
    for tool in ("why3", solver_name):
        item = data["tools_sha256"][tool]
        path = Path(item["path"])
        require(path.is_file() and sha(path) == item["sha256"], f"{tool} binary hash mismatch")
    unresolved_items = data.get("unresolved_results")
    require(isinstance(unresolved_items, list) and unresolved_items
            and data.get("unresolved_result_count") == len(unresolved_items),
            "incomplete report has no accounted unresolved results")

    all_leaves = set()
    root_total = closed_total = 0
    expected_unresolved = set()
    for target_name, target in targets.items():
        coma = Path(target.get("coma", ""))
        require(coma.is_file() and sha(coma) == target.get("coma_sha256"),
                f"Coma hash mismatch: {target_name}")
        original = target.get("original_roots")
        roots = target.get("roots")
        require(isinstance(original, list) and isinstance(roots, list),
                f"missing root accounting: {target_name}")
        require(target.get("root_count") == len(original), f"root count mismatch: {target_name}")
        root_total += len(original)
        listing_exit = target.get("why3_root_listing_exit_code")
        check_log(base, target.get("why3_root_listing"), "root listing", [])
        if target.get("target_error"):
            require(listing_exit != 0 or not original
                    or len(set(original)) != len(original),
                    f"root-listing error lacks a failed/empty inventory: {target_name}")
            expected_unresolved.add((target_name, None, None, "root-listing-error"))
            continue
        require(listing_exit == 0 and len(roots) == len(original)
                and [root.get("root") for root in roots] == original,
                f"root map mismatch: {target_name}")
        listing_stdout = base / safe_rel(target["why3_root_listing"]["stdout"]["path"])
        theory_name = None
        printed = []
        for line in listing_stdout.read_text().splitlines():
            m = re.match(r"^theory (\S+)$", line)
            if m:
                theory_name = m.group(1)
            m = re.match(r"^  goal (\S+)\s*:", line)
            if m:
                printed.append(f"{theory_name}.{m.group(1)}")
        require(printed == original, f"original goal listing mismatch: {target_name}")
        target_closed = 0
        target_open = []
        for root in roots:
            root_name = root["root"]
            status = root.get("status")
            require(status in {"closed", "open", "export-error", "empty-export"},
                    f"unknown root status: {target_name}:{root_name}")
            leaves = root.get("leaves")
            require(isinstance(leaves, list), f"missing leaf inventory: {target_name}:{root_name}")
            transform = check_log(base, root.get("transformed_export"), "transformed export",
                                  ["compute_specified", "split_vc", "Z3"])
            require(str(coma) in transform and root_name.rsplit(".", 1)[0] in transform
                    and root_name.rsplit(".", 1)[1] in transform,
                    f"transformed root command mismatch: {target_name}:{root_name}")
            export_mode = root.get("export_mode")
            if export_mode == "untransformed-fallback":
                closure = check_log(base, root.get("closure_export"), "closure export", ["Z3"])
                require(str(coma) in closure and "compute_specified" not in closure
                        and "split_vc" not in closure,
                        f"closure export command mismatch: {target_name}:{root_name}")
            elif export_mode != "transformed":
                require(status == "export-error", "invalid export mode on root error")
            if status == "closed":
                require(leaves and all(leaf.get("closure_status") == "unsat" for leaf in leaves),
                        f"closed root contains unresolved leaves: {target_name}:{root_name}")
                target_closed += 1
            else:
                target_open.append(root_name)
                if status in {"export-error", "empty-export"}:
                    expected_unresolved.add((target_name, root_name, None, status))
                elif not leaves:
                    expected_unresolved.add((target_name, root_name, None, "empty-leaf-set"))
            if status == "export-error":
                if export_mode == "transformed":
                    require(root.get("transformed_exit_code") not in (None, 0),
                            f"transformed export error has successful exit: {target_name}:{root_name}")
                else:
                    require(root.get("closure_exit_code") not in (None, 0),
                            f"fallback export error has successful exit: {target_name}:{root_name}")
            if status == "empty-export":
                require(export_mode == "untransformed-fallback" and not leaves
                        and root.get("closure_exit_code") == 0,
                        f"empty-export status is unsupported by output: {target_name}:{root_name}")
            for leaf in leaves:
                rel = safe_rel(leaf["path"])
                require(rel not in all_leaves, f"duplicate SMT mapping: {rel}")
                all_leaves.add(rel)
                smt = base / rel
                require(smt.is_file() and sha(smt) == leaf.get("sha256"), f"SMT hash mismatch: {rel}")
                status = leaf.get("status")
                require(status in {"unsat", "sat", "unknown", "timeout", "error"},
                        f"invalid solver status: {rel}")
                for key, hash_key in (("solver_command", "solver_command_sha256"),
                                      ("solver_stdout", "solver_stdout_sha256"),
                                      ("solver_stderr", "solver_stderr_sha256")):
                    path = base / safe_rel(leaf[key])
                    require(path.is_file() and sha(path) == leaf.get(hash_key), f"solver artifact hash mismatch: {path}")
                command = read(base / safe_rel(leaf["solver_command"]))
                require(isinstance(command, list) and Path(command[0]).name == solver_name,
                        f"unexpected solver command: {rel}")
                stdout = (base / safe_rel(leaf["solver_stdout"])).read_text()
                statuses = [line.strip() for line in stdout.splitlines()
                            if line.strip() in {"sat", "unsat", "unknown", "timeout"}]
                if status in {"unsat", "sat", "unknown"}:
                    require(statuses == [status], f"solver status/output mismatch: {rel}")
                    if status != "timeout":
                        require(leaf.get("exit_code") == 0,
                                f"solver status has nonzero exit code: {rel}")
                else:
                    require(status == "timeout" or
                            (status == "error" and (leaf.get("exit_code") not in (None, 0)
                             or len(statuses) != 1 or "(error" in stdout.lower())),
                            f"error status/output mismatch: {rel}")
                    if status == "timeout":
                        require(leaf.get("exit_code") in (None, 0),
                                f"timeout leaf has an invalid solver exit code: {rel}")
                        if leaf.get("exit_code") == 0:
                            require(solver_name == "z3" and statuses == ["timeout"],
                                    f"native solver timeout has inconsistent output: {rel}")
                reduced_rel = audit_ground_fallback(base, leaf, solver_name, data["time_limit_seconds"],
                                                    data.get("bundle_origin_path"))
                require(data["ground_fallback_enabled"] or leaf.get("ground_fallback") is None,
                        "fallback evidence exists although fallback was disabled")
                if reduced_rel is not None:
                    require(reduced_rel not in all_leaves, f"duplicate fallback SMT mapping: {reduced_rel}")
                    all_leaves.add(reduced_rel)
                if leaf.get("closure_status") != "unsat":
                    expected_unresolved.add((target_name, root_name, rel.as_posix(), status))
        require(target.get("closed_root_goals") == target_closed
                and target.get("open_root_goals") == target_open,
                f"target root status count mismatch: {target_name}")
        closed_total += target_closed

    smt_inventory = data.get("smt_inventory_sha256")
    actual_smt = {p.relative_to(base).as_posix(): sha(p) for p in sorted(base.rglob("*.smt2"))}
    require(smt_inventory == actual_smt and set(actual_smt) == {path.as_posix() for path in all_leaves},
            "attempt report SMT export inventory mismatch")
    require(data.get("original_root_goal_count") == root_total
            and data.get("closed_root_goal_count") == closed_total,
            "attempt report root totals mismatch")
    require(data.get("open_root_goals") == sorted(f"{t}.{r}" for t, item in targets.items()
                                                   for r in item.get("open_root_goals", [])),
            "attempt report open-root inventory mismatch")
    recorded_unresolved = set()
    for item in unresolved_items:
        require(isinstance(item, dict) and isinstance(item.get("target"), str)
                and isinstance(item.get("status"), str), "malformed unresolved-result record")
        leaf = item.get("leaf")
        recorded_unresolved.add((item["target"], item.get("root"),
                                 safe_rel(leaf).as_posix() if leaf is not None else None,
                                 item["status"]))
    require(len(recorded_unresolved) == len(unresolved_items)
            and recorded_unresolved == expected_unresolved,
            "unresolved-result list does not account for every open/error result")

    snapshot = base / safe_rel(data.get("precompile_snapshot_file", "inputs-before.json"))
    require(snapshot.is_file() and sha(snapshot) == data.get("precompile_snapshot_sha256"),
            "attempt report precompile snapshot hash mismatch")
    for key, filename in (("compile_log_sha256", "compile.log"),
                          ("clean_log_sha256", "clean.log"),
                          ("native_differential", "differential.log")):
        path = base / filename
        if key == "native_differential":
            item = data.get(key)
            require(path.is_file() and sha(path) == item.get("log_sha256")
                    and item.get("summary", {}).get("status") == "passed",
                    "attempt report native differential mismatch")
        else:
            require(path.is_file() and sha(path) == data.get(key), f"{filename} hash mismatch")
    require(data.get("selected_proof_complete") is False, "incomplete report claims proof completeness")
    return {"status": "audited-incomplete", "selected_targets": len(targets),
            "original_root_goals": root_total, "closed_root_goals": closed_total,
            "open_root_goals": len(data["open_root_goals"]),
            "unresolved_results": len(unresolved_items), "smt_leaves": len(all_leaves),
            "current_source_freshness": True,
            "limitations": data.get("limitations")}


def audit(version, manifest_path):
    manifest_path = manifest_path.resolve()
    base = manifest_path.parent
    manifest_hash = sha(manifest_path)
    data = read(manifest_path)
    if data.get("schema") == "direct-solver-attempt-report-v1":
        return audit_attempt(version, manifest_path, data)
    require(data.get("schema") == "direct-solver-evidence-v1", "wrong direct evidence schema")
    require(data.get("status") == "passed" and data.get("mode") == "socket-free-direct-solver",
            "bundle is not a successful direct-solver run")
    require(type(data.get("ground_fallback_enabled")) is bool,
            "bundle lacks explicit ground-fallback setting")
    recorded_inputs = data.get("inputs_sha256")
    require(isinstance(recorded_inputs, dict) and recorded_inputs, "missing input fingerprints")
    inputs_after = data.get("inputs_after_sha256")
    require(isinstance(inputs_after, dict) and inputs_after, "missing post-run input fingerprints")
    actual_inputs = input_hashes(version)
    require(inputs_after == actual_inputs, "post-run input fingerprint inventory or hash mismatch")
    changed_inputs = sorted(name for name in set(recorded_inputs) | set(inputs_after)
                            if recorded_inputs.get(name) != inputs_after.get(name))
    require(data.get("source_inputs_changed_during_run") == changed_inputs,
            "source input change record mismatch")
    require(data.get("current_source_freshness") is False or not changed_inputs,
            "fresh-source proof contains inputs changed during the run")
    require(data.get("toolchain_sha256") == tool_hashes(version),
            "complete verification tool hash inventory mismatch")
    boundary = data.get("trusted_boundary")
    require(isinstance(boundary, dict) and boundary.get("application_trusted_assumptions") == [],
            "application trusted-assumption ledger is missing or nonempty")
    require(boundary.get("contract_ledger") == "verification/assumptions.md"
            and boundary.get("application_model_source") == "crate/src/stdlib_models.rs",
            "standard-library contract provenance is missing")
    model_keys = sorted(name for name in recorded_inputs
                        if "creusot-std-0.13.0" in name
                        or "/creusot/share/why3find/packages/creusot/" in name)
    require(boundary.get("model_inputs_sha256_keys") == model_keys
            and "crate/src/stdlib_models.rs" in recorded_inputs
            and "verification/assumptions.md" in recorded_inputs,
            "trusted-boundary model sources are not fully fingerprinted")
    target_inventory = read(version / "verification/target-inventory.json")
    selected_contracts = target_inventory["selected"]
    selected_names = sorted(selected_contracts)
    targets = data.get("selected_targets")
    require(isinstance(targets, dict) and targets, "missing selected target records")
    require(set(targets) <= set(selected_contracts), "bundle includes unselected or unknown targets")
    require(data.get("selected_target_count") == len(targets), "selected target count mismatch")
    attempted = sorted(targets)
    deferred = sorted(set(selected_names) - set(attempted))
    require(data.get("selected_inventory_targets") == selected_names
            and data.get("selected_inventory_target_count") == len(selected_names),
            "recorded selected inventory differs from current target classification")
    require(data.get("attempted_selected_targets") == attempted
            and data.get("deferred_selected_targets") == deferred,
            "attempted/deferred selected target classification mismatch")
    complete = not deferred
    require(data.get("selected_proof_complete") is complete
            and data.get("proof_scope") == ("complete-selected-inventory" if complete
                                              else "selected-target-subset"),
            "selected proof completeness/scope label mismatch")
    require(data.get("expected_open_targets") == sorted(target_inventory.get("expected_open", {}))
            and data.get("excluded_generated_targets") == sorted(target_inventory.get("excluded_generated", {})),
            "expected-open/excluded classification differs from target inventory")
    generated_targets = data.get("generated_target_inventory")
    require(isinstance(generated_targets, dict)
            and data.get("generated_target_count") == len(generated_targets),
            "missing generated target inventory")
    expected_open_names = set(target_inventory.get("expected_open", {}))
    excluded_names = set(target_inventory.get("excluded_generated", {}))
    generated_classifications = {}
    for name, item in generated_targets.items():
        category = ("selected" if name in selected_contracts else
                    "expected-open" if name in expected_open_names else
                    "excluded" if name in excluded_names else "unclassified")
        require(item.get("classification") == category,
                f"generated target classification mismatch: {name}")
        path = Path(item.get("path", ""))
        require(path.is_file() and sha(path) == item.get("sha256"),
                f"generated target file hash mismatch: {name}")
        generated_classifications[name] = category
    complete_generated = data.get("complete_generated_inventory_checked") is True
    if complete_generated:
        complete_inventory = set(selected_names) | expected_open_names | excluded_names
        require(set(generated_targets) == complete_inventory,
                "complete generated inventory differs from selected/open/excluded classification")

    solver_name = data.get("solver")
    require(solver_name in {"z3", "cvc5"}, "unknown solver")
    tool_records = data.get("tools_sha256")
    require(isinstance(tool_records, dict) and set(tool_records) == {"why3", solver_name},
            "wrong tool fingerprint inventory")
    for name, item in tool_records.items():
        path = Path(item["path"])
        require(path.is_file() and sha(path) == item["sha256"], f"tool binary hash mismatch: {name}")

    all_leaves = set()
    total_roots = total_closed = 0
    for name, target in targets.items():
        require(target.get("coma_sha256") and Path(target["coma"]).is_file()
                and sha(Path(target["coma"])) == target["coma_sha256"], f"Coma hash mismatch: {name}")
        original = target.get("original_roots")
        roots = target.get("roots")
        require(isinstance(original, list) and original and len(original) == len(set(original)),
                f"invalid original root list: {name}")
        require(isinstance(roots, list) and len(roots) == len(original), f"root mapping count mismatch: {name}")
        mapped = [root.get("root") for root in roots]
        require(mapped == original, f"original-root to export mapping mismatch: {name}")
        require(target.get("root_count") == len(original), f"root count mismatch: {name}")
        require(target.get("closed_root_goals") == len(original) and target.get("open_root_goals") == [],
                f"selected target is not fully closed: {name}")
        total_roots += len(original)
        total_closed += len(original)
        original_cmd = check_log(base, target.get("why3_root_listing"), "root listing", [])
        require(target["coma"] in original_cmd, f"root listing does not read recorded Coma: {name}")
        listing_stdout = base / safe_rel(target["why3_root_listing"]["stdout"]["path"])
        theory_name = None
        listed_roots = []
        for line in listing_stdout.read_text().splitlines():
            match = re.match(r"^theory (\S+)$", line)
            if match:
                theory_name = match.group(1)
            match = re.match(r"^  goal (\S+)\s*:", line)
            if match:
                require(theory_name is not None, f"root listing goal lacks theory: {name}")
                listed_roots.append(f"{theory_name}.{match.group(1)}")
        require(listed_roots == original, f"root listing does not match recorded complete roots: {name}")
        for root in roots:
            mode = root.get("export_mode")
            require(mode in {"transformed", "untransformed-fallback"}, f"bad export mode: {name}:{root['root']}")
            leaves = root.get("leaves")
            require(isinstance(leaves, list) and leaves, f"no SMT leaves for root: {name}:{root['root']}")
            transformed_count = root.get("transformed_leaf_count")
            require(type(transformed_count) is int and transformed_count >= 0, "invalid transformed leaf count")
            require((mode == "transformed" and transformed_count == len(leaves))
                    or (mode == "untransformed-fallback" and transformed_count == 0),
                    f"export-mode/leaf-count mismatch: {name}:{root['root']}")
            theory, goal = root["root"].rsplit(".", 1)
            transform_cmd = check_log(base, root.get("transformed_export"), "transformed export",
                                      ["compute_specified", "split_vc", "Z3"])
            require(target["coma"] in transform_cmd and theory in transform_cmd and goal in transform_cmd,
                    f"transformed command root mismatch: {name}:{root['root']}")
            closure_record = root.get("closure_export")
            if mode == "untransformed-fallback":
                closure_cmd = check_log(base, closure_record, "closure export", ["Z3"])
                require(target["coma"] in closure_cmd and theory in closure_cmd and goal in closure_cmd,
                        f"closure command root mismatch: {name}:{root['root']}")
                require("compute_specified" not in closure_cmd and "split_vc" not in closure_cmd,
                        "fallback closure export unexpectedly applied transformations")
            else:
                require(closure_record is None, "transformed root has unexpected closure export")
            for leaf in leaves:
                rel = safe_rel(leaf["path"])
                require(rel not in all_leaves, f"SMT leaf mapped more than once: {rel}")
                all_leaves.add(rel)
                smt = base / rel
                require(smt.is_file() and sha(smt) == leaf["sha256"], f"SMT hash mismatch: {rel}")
                require(leaf.get("closure_status") == "unsat",
                        f"solver leaf not closed: {rel}")
                stdout_rel = safe_rel(leaf["solver_stdout"])
                stderr_rel = safe_rel(leaf["solver_stderr"])
                stdout = base / stdout_rel
                stderr = base / stderr_rel
                require(stdout.is_file() and sha(stdout) == leaf["solver_stdout_sha256"], f"solver output hash mismatch: {stdout_rel}")
                require(stderr.is_file() and sha(stderr) == leaf["solver_stderr_sha256"], f"solver stderr hash mismatch: {stderr_rel}")
                lines = [line.strip() for line in stdout.read_text().splitlines() if line.strip() in {"sat", "unsat", "unknown", "timeout"}]
                require((leaf.get("status") == "unsat" and leaf.get("exit_code") == 0
                         and lines == ["unsat"] and "(error" not in stdout.read_text().lower())
                        or (leaf.get("status") in {"timeout", "unknown"}
                            and (leaf.get("status") == "unknown" and lines == ["unknown"]
                                 and leaf.get("exit_code") == 0
                                 or leaf.get("status") == "timeout")),
                        f"original solver outcome is inconsistent: {stdout_rel}")
                cmd = read(base / safe_rel(leaf["solver_stdout"]).parent / "command.json")
                solver_command = base / safe_rel(leaf["solver_command"])
                require(solver_command.is_file() and sha(solver_command) == leaf["solver_command_sha256"],
                        f"solver command hash mismatch: {rel}")
                require(read(solver_command) == cmd, f"duplicate solver command records differ: {rel}")
                require(isinstance(cmd, list) and cmd and Path(cmd[0]).name == solver_name,
                        f"unexpected solver command for {rel}")
                reduced_rel = audit_ground_fallback(base, leaf, solver_name, data["time_limit_seconds"],
                                                    data.get("bundle_origin_path"))
                require(data["ground_fallback_enabled"] or leaf.get("ground_fallback") is None,
                        "fallback evidence exists although fallback was disabled")
                if reduced_rel is not None:
                    require(reduced_rel not in all_leaves, f"fallback SMT mapped more than once: {reduced_rel}")
                    all_leaves.add(reduced_rel)

    inventory = data.get("smt_inventory_sha256")
    actual_smt = {p.relative_to(base).as_posix(): sha(p) for p in sorted(base.rglob("*.smt2"))}
    require(inventory == actual_smt, "complete SMT export inventory mismatch")
    require(set(inventory) == {p.as_posix() for p in all_leaves}, "unmapped SMT exports are present")
    require(data.get("original_root_goal_count") == total_roots
            and data.get("closed_root_goal_count") == total_closed, "global root totals mismatch")
    require(data.get("open_root_goals") == [], "bundle records open root goals")
    if data.get("current_source_freshness") is True:
        require(complete, "fresh-source bundle omitted selected targets")
        require(complete_generated, "fresh-source bundle did not check complete generated inventory")
        require(isinstance(data.get("fresh_compile_command"), str)
                and data.get("precompile_snapshot_sha256"), "fresh compile provenance is incomplete")
        snapshot_rel = safe_rel(data.get("precompile_snapshot_file", "inputs-before.json"))
        snapshot = base / snapshot_rel
        require(snapshot.is_file() and sha(snapshot) == data["precompile_snapshot_sha256"],
                "pre-compile snapshot hash mismatch")
        for key in ("native_differential",):
            item = data.get(key)
            require(isinstance(item, dict) and isinstance(item.get("summary"), dict)
                    and item["summary"].get("status") == "passed",
                    "fresh run is missing a passing native differential")
            log = base / "differential.log"
            require(log.is_file() and sha(log) == item.get("log_sha256"),
                    "native differential log hash mismatch")
        native_hashes = data.get("native_checks_sha256", {})
        require(set(native_hashes) == {"tests.log", "check-alloc.log"},
                "native unit/doc and alloc checks are missing")
        for name, digest in native_hashes.items():
            require((base / name).is_file() and sha(base / name) == digest,
                    f"native check log hash mismatch: {name}")
        require("test result: ok." in (base / "tests.log").read_text(),
                "native unit/doc test result is missing")
        for key, filename in (("compile_log_sha256", "compile.log"),
                              ("clean_log_sha256", "clean.log")):
            path = base / filename
            require(path.is_file() and sha(path) == data.get(key), f"{filename} hash mismatch")
    require(sha(manifest_path) == manifest_hash, "manifest changed during audit")
    return {"status": "passed", "selected_targets": len(targets),
            "selected_inventory_targets": len(selected_names),
            "deferred_selected_targets": len(deferred),
            "selected_proof_complete": complete,
            "proof_scope": data["proof_scope"],
            "generated_target_count": len(generated_targets),
            "complete_generated_inventory_checked": complete_generated,
            "original_root_goals": total_roots, "closed_root_goals": total_closed,
            "smt_leaves": len(all_leaves), "input_files_checked": len(actual_inputs),
            "current_source_freshness": data.get("current_source_freshness"),
            "source_inputs_changed_during_run": changed_inputs,
            "limitations": data.get("limitations")}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("version_directory", type=Path)
    ap.add_argument("--manifest", type=Path, required=True)
    args = ap.parse_args()
    print(json.dumps(audit(args.version_directory.resolve(), args.manifest.resolve()), indent=2))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
