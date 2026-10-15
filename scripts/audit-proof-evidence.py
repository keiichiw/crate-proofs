#!/usr/bin/env python3
"""Read-only audit of a Creusot/why3find saved-evidence manifest and sessions."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def unique_pairs(pairs):
    result = {}
    for name, value in pairs:
        require(name not in result, f"Duplicate JSON key: {name}")
        result[name] = value
    return result


def read_json(path):
    return json.loads(path.read_text(), object_pairs_hook=unique_pairs)


def closed(tree):
    if not isinstance(tree, dict) or not tree:
        return False
    if "prover" in tree:
        return isinstance(tree["prover"], str) and bool(tree["prover"].strip())
    if "tactic" in tree:
        return (isinstance(tree["tactic"], str) and bool(tree["tactic"])
                and isinstance(tree.get("children"), list) and bool(tree["children"])
                and all(closed(child) for child in tree["children"]))
    return all(isinstance(children, list) and bool(children) and all(map(closed, children))
               for children in tree.values())


def target_path(name):
    require(isinstance(name, str) and bool(name), "Invalid target name")
    path = PurePosixPath(name)
    require(not path.is_absolute() and ".." not in path.parts and str(path) == name,
            f"Unsafe/noncanonical target path: {name}")
    return Path(*path.parts)


def reconstruct(path, args):
    home = os.environ.get("XDG_DATA_HOME")
    config = args.why3_config or (Path(home) / "creusot/creusot_why3.conf" if home else None)
    libraries = args.why3_library or ([Path(home) / "creusot/share/why3find/packages/creusot"] if home else [])
    require(config and libraries, "Activate the environment or supply --why3-config and --why3-library")
    command = ["why3", "prove", "-C", str(config)]
    for library in libraries:
        command += ["-L", str(library)]
    result = subprocess.run(command + [str(path)], check=True, capture_output=True,
                            text=True, timeout=30)
    roots = set()
    module = None
    for line in result.stdout.splitlines():
        header = re.match(r"^theory (\S+)$", line)
        if header:
            module = header.group(1)
        goal = re.match(r"^  goal (\S+)\s*:", line)
        if goal:
            require(module is not None, f"Why3 goal without theory: {path}")
            qualified = f"{module}.{goal.group(1)}"
            require(qualified not in roots, f"Duplicate reconstructed root: {qualified}")
            roots.add(qualified)
    require(bool(roots), f"Why3 reconstructed no root goals: {path}")
    return roots


def audit_session(base, name, item, expected_open, args):
    directory = base / target_path(name)
    proof = directory / "proof.json"
    coma = directory / "target.coma"
    require(sha(proof) == item["proof_json_sha256"], f"Session hash mismatch: {name}")
    require(sha(coma) == item["coma_sha256"], f"Coma hash mismatch: {name}")
    modules = read_json(proof).get("proofs")
    require(isinstance(modules, dict) and bool(modules), f"Missing/zero proof modules: {name}")
    goals = {}
    for module, group in modules.items():
        require(isinstance(group, dict) and bool(group), f"Empty/malformed proof module: {name}/{module}")
        for goal, tree in group.items():
            qualified = f"{module}.{goal}"
            require(qualified not in goals, f"Duplicate root goal: {qualified}")
            goals[qualified] = tree
    inventory = item["goal_inventory"]
    require(isinstance(inventory, list) and all(isinstance(g, str) for g in inventory)
            and len(inventory) == len(set(inventory)) and set(inventory) == set(goals),
            f"Manifest/session root inventory mismatch: {name}")
    require(type(item["goals"]) is int and item["goals"] > 0 and item["goals"] == len(goals),
            f"Missing/zero/wrong root goal count: {name}")
    text = coma.read_text()
    function = name.rsplit("/", 1)[-1]
    if function.endswith("__refines"):
        target_vc = "refines"
    else:
        explicit = re.findall(r"^goal (vc_\w+):", text, re.MULTILINE)
        bodies = re.findall(r"^let (?:rec )?(\w+) ", text, re.MULTILINE)
        require(explicit or bodies, f"No recognizable Creusot target declaration: {name}")
        target_vc = explicit[-1] if explicit else "vc_" + bodies[-1]
    require(any(g.rsplit(".", 1)[-1] == target_vc for g in goals), f"Missing target VC: {name}")
    unresolved = sorted(g for g, tree in goals.items() if not closed(tree))
    require(isinstance(item["open_goals"], list) and sorted(item["open_goals"]) == unresolved,
            f"Open goal status mismatch: {name}")
    if expected_open:
        require(bool(unresolved) and isinstance(item.get("reason"), str) and bool(item["reason"].strip()),
                f"Expected-open target must remain open and explain why: {name}")
    else:
        require(not unresolved, f"Selected target has open goals: {name}")
    if args.reconstruct_root_goals:
        require(reconstruct(coma, args) == set(goals), f"Why3/session root inventory mismatch: {name}")
    return len(goals)


def audit(args):
    version = args.version_directory.resolve()
    manifest_path = (args.manifest or version / "verification/evidence/latest/manifest.json").resolve()
    base = manifest_path.parent
    manifest_before = sha(manifest_path)
    record = read_json(manifest_path)
    require(record.get("cache") is False, "Manifest must explicitly record cache=false")
    inputs = record["inputs_sha256"]
    require(isinstance(inputs, dict) and bool(inputs), "Missing input fingerprints")
    for name, expected in inputs.items():
        path = Path(name)
        if not path.is_absolute():
            path = version / path
        require(sha(path) == expected, f"Input hash mismatch: {name}")
    recorded_paths = {Path(os.path.abspath(Path(name) if Path(name).is_absolute() else version / name))
                      for name in inputs}
    source_roots = args.source_root or [version / "crate/src"]
    for source_root in source_roots:
        require(source_root.is_dir(), f"Source root missing; supply --source-root for another layout: {source_root}")
        sources = {Path(os.path.abspath(path)) for path in source_root.rglob("*.rs")}
        require(bool(sources) and sources <= recorded_paths,
                f"Rust source inventory missing from fingerprints: {sorted(str(p) for p in sources - recorded_paths)}")
    positive = record["targets"]
    opened = record.get("expected_open", {})
    excluded = record.get("excluded_generated", {})
    require(isinstance(positive, dict) and bool(positive) and isinstance(opened, dict)
            and isinstance(excluded, dict), "Missing/malformed target classifications")
    require(all(isinstance(reason, str) and bool(reason.strip()) for reason in excluded.values()),
            "Excluded generated targets need a nonempty reason")
    require(not (positive.keys() & opened.keys() or positive.keys() & excluded.keys()
                 or opened.keys() & excluded.keys()), "Target classifications overlap")
    classified = set(positive) | set(opened) | set(excluded)
    for name in classified:
        target_path(name)
    require(type(record["generated_target_count"]) is int
            and record["generated_target_count"] == len(classified), "Generated target count mismatch")
    sessions = {p.parent.relative_to(base).as_posix() for p in base.rglob("proof.json")}
    coma_targets = {p.parent.relative_to(base).as_posix() for p in base.rglob("target.coma")}
    require(sessions == coma_targets == set(positive) | set(opened), "Saved target inventory mismatch")
    total = sum(audit_session(base, name, item, False, args) for name, item in positive.items())
    require(type(record["total_session_goals"]) is int and total == record["total_session_goals"],
            "Selected root goal total mismatch")
    for name, item in opened.items():
        audit_session(base, name, item, True, args)
    if opened:
        require((base / "open-prove.exit").read_text().strip() == "1", "Expected-open prover exit must be 1")
    if args.generated_dir:
        generated = {p.relative_to(args.generated_dir).as_posix().removesuffix(".coma")
                     for p in args.generated_dir.rglob("*.coma")}
        require(generated == classified, "Complete generated Coma inventory mismatch")
    require(sha(manifest_path) == manifest_before, "Manifest changed during audit")
    # Recheck inputs and saved sessions, so a mid-audit change is not overlooked.
    for name, expected in inputs.items():
        path = Path(name)
        require(sha(path if path.is_absolute() else version / path) == expected, f"Input changed during audit: {name}")
    for name, item in {**positive, **opened}.items():
        directory = base / target_path(name)
        require(sha(directory / "proof.json") == item["proof_json_sha256"]
                and sha(directory / "target.coma") == item["coma_sha256"], f"Session changed during audit: {name}")
    return {"status": "passed", "manifest_sha256": manifest_before,
            "selected_targets": len(positive), "closed_root_goals": total,
            "expected_open_targets": len(opened), "excluded_generated_targets": len(excluded),
            "why3_root_reconstruction": args.reconstruct_root_goals,
            "complete_generated_inventory_checked": bool(args.generated_dir),
            "limitations": "Checks saved record consistency against current inputs; does not run provers, recheck certificates, prove upstream equivalence, or establish freshness independently of the recorded run."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("version_directory", type=Path)
    parser.add_argument("--manifest", type=Path, help="alternate saved bundle manifest")
    parser.add_argument("--source-root", type=Path, action="append", help="Rust source tree to inventory (default VERSION/crate/src)")
    parser.add_argument("--generated-dir", type=Path, help="optional complete fresh Coma root, including excluded targets")
    parser.add_argument("--reconstruct-root-goals", action="store_true")
    parser.add_argument("--why3-config", type=Path)
    parser.add_argument("--why3-library", type=Path, action="append")
    args = parser.parse_args()
    print(json.dumps(audit(args), indent=2))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
