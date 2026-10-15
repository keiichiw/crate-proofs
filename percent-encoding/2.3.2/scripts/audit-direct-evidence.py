#!/usr/bin/env python3
"""Independently audit a fresh percent-encoding direct-SMT evidence bundle."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys


def require(ok, message):
    if not ok: raise ValueError(message)


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""): h.update(block)
    return h.hexdigest()


def helper(version):
    spec = importlib.util.spec_from_file_location("check_proofs", version / "scripts/check-proofs.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def safe(base, value):
    path = Path(value)
    require(value and not path.is_absolute() and ".." not in path.parts,
            f"unsafe bundle path: {value}")
    result = base / path
    require(result.is_file(), f"missing evidence artifact: {result}")
    return result


def check_process(base, record, expected_tool):
    require(isinstance(record, dict) and set(record) == {"command.json", "stdout.txt", "stderr.txt"},
            "incomplete logged process record")
    paths = {}
    for key, value in record.items():
        path = safe(base, value["path"])
        require(sha(path) == value["sha256"], f"logged process hash mismatch: {path}")
        paths[key] = path
    cmd = json.loads(paths["command.json"].read_text())
    require(isinstance(cmd, list) and cmd and Path(cmd[0]).name == expected_tool,
            f"unexpected process command: {cmd}")
    return cmd, paths


def audit(version, manifest_path):
    manifest_path = manifest_path.resolve()
    base = manifest_path.parent
    data = json.loads(manifest_path.read_text())
    require(data.get("schema") == "percent-direct-solver-evidence-v1"
            and data.get("status") == "passed"
            and data.get("mode") == "socket-free-direct-why3-smt-z3-cvc5",
            "bundle is not a passing direct Why3/SMT/Z3/CVC5 report")
    check = helper(version)
    current = {str(p.relative_to(version) if p.is_relative_to(version) else p): check.sha(p)
               for p in check.input_paths()}
    require(data.get("inputs_sha256") == current and data.get("inputs_after_sha256") == current,
            "bundle inputs differ from current source/docs/scripts/dependency/model inputs")
    require(data.get("toolchain_sha256") == check.tool_hashes(),
            "toolchain fingerprints differ from current binaries")
    require(data.get("tool_sha256", {}).get("cvc5") == data["toolchain_sha256"].get("cvc5"),
            "manifest CVC5 binary/version identity differs from the snapshotted toolchain")
    require(isinstance(data.get("cvc5_time_limit_ms"), int) and data["cvc5_time_limit_ms"] > 0,
            "CVC5 secondary solver limit is missing or invalid")
    require(data.get("application_trusted_assumptions") == [],
            "application trusted assumptions must be empty")
    require(data.get("original_root_goal_count", 0) > 0
            and data.get("closed_root_goal_count") == data.get("original_root_goal_count"),
            "root goal count is zero or does not close")
    inventory = json.loads((version / "verification/target-inventory.json").read_text())
    selected, opened, excluded = (inventory.get("selected", {}), inventory.get("expected_open", {}),
                                  inventory.get("excluded_generated", {}))
    targets = data.get("selected_targets")
    require(isinstance(targets, dict) and set(targets) == set(selected),
            "not every selected inventory target was proved")
    generated = data.get("generated_target_inventory")
    expected_names = set(selected) | set(opened) | set(excluded)
    require(not (set(selected) & set(opened) or set(selected) & set(excluded)
                or set(opened) & set(excluded)), "target inventory classifications overlap")
    require(isinstance(generated, dict) and set(generated) == expected_names
            and data.get("generated_target_count") == len(generated),
            "generated target inventory is incomplete or unclassified")
    for name, item in generated.items():
        category = "selected" if name in selected else "expected-open" if name in opened else "excluded"
        path = safe(base, item.get("path", ""))
        require(item.get("classification") == category and path.is_file()
                and sha(path) == item.get("sha256"), f"generated Coma mismatch: {name}")
        require(Path(item.get("origin_path", "")).is_absolute(), f"missing Coma origin path: {name}")
    require(data.get("target_classification") == {"selected": sorted(selected),
        "expected_open": sorted(opened), "excluded": sorted(excluded)},
        "target classification differs from inventory")

    leaves, total_roots = set(), 0
    generated_text = "\n".join(safe(base, item["path"]).read_text(errors="replace")
                               for item in generated.values())
    # Find cross-crate model calls directly in the captured implementation. Each
    # named call must survive translation into its selected target's Coma.
    source_calls = set()
    for source in (version / "crate/src").rglob("*.rs"):
        source_calls.update(re.findall(r"\bform_model::([A-Za-z_][A-Za-z_0-9]*)", source.read_text()))
    require(source_calls, "no explicit call to the checked form_urlencoded dependency models")
    require(data.get("dependency_calls") == sorted(source_calls), "dependency call inventory differs from source")
    require({"encoded_array_model", "byte_model_subsequence"} <= source_calls,
            "source does not call the checked encoder and decoder bridge lemmas")
    require(all(re.search(rf"\b{re.escape(name)}\b", generated_text) for name in source_calls),
            f"a source-level dependency call is missing from generated Coma: {sorted(source_calls)}")

    for name, target in targets.items():
        coma = safe(base, target.get("coma_path", ""))
        require(sha(coma) == target.get("coma_sha256"), f"selected Coma hash mismatch: {name}")
        roots = target.get("roots")
        proofs = target.get("proofs")
        require(isinstance(roots, list) and roots and len(set(roots)) == len(roots)
                and isinstance(proofs, list) and [x.get("root") for x in proofs] == roots,
                f"invalid positive root inventory: {name}")
        require(target.get("root_count") == len(roots) == target.get("closed_root_goals")
                and target.get("open_root_goals") == [], f"unclosed root(s): {name}")
        total_roots += len(roots)
        listing_cmd, listing = check_process(base, target.get("root_listing"), "why3")
        origin = target.get("coma_origin_path")
        require(Path(origin).is_absolute() and origin in listing_cmd,
                f"Why3 listing reads wrong fresh Coma: {name}")
        stdout = listing["stdout.txt"].read_text()
        theory, observed = None, []
        for line in stdout.splitlines():
            match = re.match(r"^theory (\S+)$", line)
            if match: theory = match.group(1)
            match = re.match(r"^  goal (\S+)\s*:", line)
            if match:
                require(theory is not None, "goal printed before its theory")
                observed.append(f"{theory}.{match.group(1)}")
        require(observed == roots, f"Why3 root listing does not match root inventory: {name}")
        for proof in proofs:
            export = proof.get("export_command")
            if proof.get("export_mode") == "untransformed-positive-root":
                require(isinstance(export, dict) and set(export) == {"transformed", "untransformed"},
                        "missing transformed and positive untransformed root exports")
                tx_cmd, _ = check_process(base, export["transformed"], "why3")
                raw_cmd, _ = check_process(base, export["untransformed"], "why3")
                require("compute_specified" in tx_cmd and "split_vc" in tx_cmd
                        and origin in tx_cmd and origin in raw_cmd and "-P" in raw_cmd and "Z3" in raw_cmd,
                        "incorrect transformed/original root export commands")
            else:
                require(proof.get("export_mode") == "transformed", "unknown export mode")
                cmd, _ = check_process(base, export, "why3")
                require(origin in cmd and "compute_specified" in cmd and "split_vc" in cmd
                        and "-P" in cmd and "Z3" in cmd, "export is not direct Why3->SMT: " + proof["root"])
            expected_position = cmd.index("-T") if proof.get("export_mode") == "transformed" else tx_cmd.index("-T")
            root_cmd = cmd if proof.get("export_mode") == "transformed" else tx_cmd
            require(root_cmd[expected_position + 1] == proof["root"].rsplit(".", 1)[0]
                    and root_cmd[root_cmd.index("-G") + 1] == proof["root"].rsplit(".", 1)[1],
                    "export command targets a different theory or goal")
            require(proof.get("status") == "closed" and proof.get("leaf_count", 0) > 0,
                    f"root has no closed SMT leaves: {name}:{proof.get('root')}")
            for leaf in proof["leaves"]:
                smt = safe(base, leaf["path"])
                require(sha(smt) == leaf["sha256"], f"SMT hash mismatch: {smt}")
                leaves.add(Path(leaf["path"]).as_posix())
                command = safe(base, leaf["solver_command"])
                require(sha(command) == leaf.get("solver_command_sha256"), "solver command hash mismatch")
                cmd = json.loads(command.read_text())
                origin_smt = str(Path(data["bundle_origin_path"]) / leaf["path"])
                require(cmd and Path(cmd[0]).name == "z3" and origin_smt in cmd,
                        "recorded primary solver is not Z3 over the recorded SMT file")
                stdout_path = safe(base, leaf["solver_stdout"])
                stderr_path = safe(base, leaf["solver_stderr"])
                require(sha(stdout_path) == leaf.get("solver_stdout_sha256")
                        and sha(stderr_path) == leaf.get("solver_stderr_sha256"),
                        "solver stdout/stderr hash mismatch")
                stdout, stderr = stdout_path.read_text(), stderr_path.read_text()
                primary_statuses = [x.strip() for x in stdout.splitlines() if x.strip() in
                                     {"sat", "unsat", "unknown", "timeout"}]
                primary_closed = (leaf.get("primary_exit_code") == 0 and primary_statuses == ["unsat"]
                    and "(error" not in stdout.lower() and "(error" not in stderr.lower())
                require(leaf.get("primary_status") == (primary_statuses[0]
                        if len(primary_statuses) == 1 else "error"),
                        "recorded primary solver status disagrees with its raw output")
                secondary_closed = False
                secondary = leaf.get("secondary_solver")
                require(secondary is None or leaf.get("primary_status") != "sat"
                        and leaf.get("primary_status") in {"timeout", "unknown"},
                        "CVC5 fallback was used after a primary SAT/error result")
                if secondary is not None:
                    require(not primary_closed and secondary.get("name") == "cvc5",
                            "CVC5 fallback exists despite a closed primary or has wrong identity")
                    proc_record = secondary.get("process")
                    cvc5_cmd, cvc5_paths = check_process(base, proc_record, "cvc5")
                    require(len(cvc5_cmd) == 3 and cvc5_cmd[1].startswith("--tlimit=")
                            and int(cvc5_cmd[1].split("=", 1)[1]) == data.get("cvc5_time_limit_ms")
                            and origin_smt == cvc5_cmd[2],
                            "CVC5 was not run with a bounded limit on the identical SMT leaf")
                    cvc5_out = cvc5_paths["stdout.txt"].read_text()
                    cvc5_err = cvc5_paths["stderr.txt"].read_text()
                    cvc5_statuses = [x.strip() for x in cvc5_out.splitlines() if x.strip() in
                                      {"sat", "unsat", "unknown", "timeout"}]
                    secondary_closed = (secondary.get("exit_code") == 0 and cvc5_statuses == ["unsat"]
                        and "(error" not in cvc5_out.lower() and "(error" not in cvc5_err.lower())
                    require(secondary.get("status") == (cvc5_statuses[0]
                            if len(cvc5_statuses) == 1 else "error")
                            and secondary.get("closed_original_smt") == secondary_closed,
                            "recorded CVC5 status disagrees with its raw output")
                require(leaf.get("status") == "unsat" and leaf.get("exit_code") == 0 and
                        ((primary_closed and leaf.get("final_solver") == "z3" and secondary is None)
                         or (secondary_closed and leaf.get("final_solver") == "cvc5")),
                        f"leaf was not closed by Z3 or secondary CVC5 UNSAT: {leaf['path']}")
    require(total_roots == data["original_root_goal_count"], "aggregate positive root count mismatch")
    actual_smt = {p.relative_to(base).as_posix() for p in base.rglob("*.smt2")}
    require(actual_smt == leaves, "SMT files on disk differ from the complete recorded leaf inventory")
    require(data.get("smt_inventory_sha256") == {p: sha(safe(base, p)) for p in sorted(leaves)},
            "SMT inventory differs from root leaf set")
    require(data.get("selected_target_count") == len(targets), "selected target count mismatch")
    require(data.get("dependency_evidence", {}).get("status") == "passed"
            and data.get("dependency_evidence", {}).get("selected_targets"),
            "pinned dependency audit is absent or empty")
    dep_audit = safe(base, "dependency-audit.json")
    require(sha(dep_audit) == data.get("dependency_audit_sha256")
            and json.loads(dep_audit.read_text()) == data["dependency_evidence"],
            "dependency evidence audit hash/content mismatch")
    metadata = safe(base, "cargo-metadata.json")
    require(sha(metadata) == data.get("cargo_metadata_sha256"), "Cargo metadata log hash mismatch")
    cargo = json.loads(metadata.read_text())
    packages = cargo.get("packages", [])
    form = next((p for p in packages if p.get("name") == "form_urlencoded" and p.get("version") == "1.2.2"), None)
    percent = next((p for p in packages if p.get("name") == "percent-encoding" and p.get("version") == "2.3.2"
                    and isinstance(p.get("source"), str) and p["source"].startswith("registry+")), None)
    require(form and form.get("source") is None and
            Path(form["manifest_path"]).resolve() ==
            (version.parent.parent / "form_urlencoded/1.2.2/crate/Cargo.toml").resolve(),
            "Cargo metadata does not pin the intended local form dependency")
    require(percent, "Cargo metadata is missing the registry percent-encoding package")
    package_by_id = {p["id"]: p for p in packages}
    form_node = next((node for node in cargo.get("resolve", {}).get("nodes", [])
                      if node.get("id") == form.get("id")), None)
    require(form_node is not None, "Cargo metadata lacks the local form dependency graph node")
    percent_edges = [package_by_id[dep["pkg"]] for dep in form_node.get("deps", [])
                     if dep.get("pkg") in package_by_id
                     and package_by_id[dep["pkg"]].get("name") == "percent-encoding"]
    require(any(p.get("source") == percent.get("source") for p in percent_edges),
            "form_urlencoded's percent-encoding edge is not the registry package")
    for artifact, field in (("compile.log", "compile_log_sha256"),
                            ("differential.log", "differential_log_sha256"),
                            ("inputs-before.json", "snapshot_sha256")):
        path = safe(base, artifact)
        require(sha(path) == data.get(field), f"{artifact} hash mismatch")
    native = data.get("native_evidence")
    require(isinstance(native, dict)
            and isinstance(native.get("run_id"), str)
            and native["run_id"].startswith("percent-encoding-2.3.2-full-scope-")
            and native["run_id"] != "percent-encoding-2.3.2-full-scope-",
            "full-scope native evidence identity is missing")
    native_rel = Path("native-evidence")
    require(not native_rel.is_absolute() and ".." not in native_rel.parts,
            "unsafe native evidence directory path")
    native_dir = base / native_rel
    require(native_dir.is_dir(), "native evidence directory is missing")
    expected_native = {
        "differential-run-full-scope.log", "fork-unit-all-features-full-scope.log",
        "fork-doc-all-features-full-scope.log", "fork-check-default-full-scope.log",
        "fork-check-bare-full-scope.log", "fork-check-alloc-full-scope.log",
        "upstream-unit-all-features-full-scope.log", "source-fingerprint.txt",
    }
    require({p.name for p in native_dir.iterdir() if p.is_file()} == expected_native,
            "native evidence log inventory mismatch")
    native_hashes = native.get("logs_sha256")
    require(isinstance(native_hashes, dict) and set(native_hashes) == expected_native,
            "native evidence hashes are incomplete")
    for name in expected_native:
        path = safe(native_dir, name)
        require(sha(path) == native_hashes[name], f"native evidence hash mismatch: {name}")
        if name != "source-fingerprint.txt":
            lines = path.read_text(errors="replace").splitlines()
            require(bool(lines) and lines[0] == f"RUN_ID={native['run_id']}",
                    f"native log run ID mismatch: {name}")
    differential_lines = safe(native_dir, "differential-run-full-scope.log").read_text().splitlines()
    summaries = [json.loads(line) for line in differential_lines if line.startswith("{")]
    require(len(summaries) == 1 and summaries[0].get("run_id") == native["run_id"]
            and summaries[0].get("status") == "passed"
            and summaries[0].get("invalid_owned_utf8_error_checks", 0) >= 6,
            "native differential summary lacks passing strict UTF-8 observables")
    fingerprint = safe(native_dir, "source-fingerprint.txt").read_text().splitlines()
    require(fingerprint and fingerprint[0] == f"RUN_ID={native['run_id']}"
            and "BEFORE" in fingerprint and "AFTER" in fingerprint,
            "native source/config fingerprint is absent")
    before_i, after_i = fingerprint.index("BEFORE"), fingerprint.index("AFTER")
    require(fingerprint[before_i + 1:after_i] == fingerprint[after_i + 1:],
            "native source/config fingerprint changed during run")
    snapshot_inputs = data.get("inputs_sha256", {})
    repo_root = version.parent.parent.resolve()
    for row in fingerprint[before_i + 1:after_i]:
        parts = row.split(None, 1)
        require(len(parts) == 2 and len(parts[0]) == 64,
                f"malformed native fingerprint row: {row!r}")
        path = (repo_root / parts[1]).resolve()
        key = str(path.relative_to(version)) if path.is_relative_to(version) else str(path)
        require(snapshot_inputs.get(key) == parts[0],
                f"native source fingerprint differs from evidence input snapshot: {parts[1]}")
    command = data.get("compile_command")
    require(isinstance(command, list) and "--offline" in command and "--locked" in command
            and "--" in command and Path(data.get("compile_cwd", "")).resolve() ==
            (version / "crate").resolve(),
            "compile command was not locked and offline")
    return {"status": "passed", "selected_targets": len(targets),
            "generated_targets": len(generated), "positive_root_goals": total_roots,
            "smt_leaves": len(leaves), "dependency_symbols_seen_in_coma": sorted(source_calls)}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("version_directory", type=Path)
    ap.add_argument("--manifest", type=Path, required=True)
    args = ap.parse_args()
    print(json.dumps(audit(args.version_directory.resolve(), args.manifest.resolve()), indent=2))


if __name__ == "__main__":
    try: main()
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
