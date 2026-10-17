#!/usr/bin/env python3
"""Fingerprint inputs and assemble/audit a fresh form_urlencoded proof bundle."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys


def digest(path):
    value = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def version_root():
    return Path(__file__).resolve().parent.parent


def repo_root(version):
    return version.parent.parent


def add_tree(paths, root, suffixes=None):
    root = Path(root)
    if root.exists():
        paths.update(p for p in root.rglob("*") if p.is_file()
                     and (suffixes is None or p.suffix in suffixes))


def input_paths(version):
    repo = repo_root(version)
    paths = set()
    for relative in (
        "Cargo.toml", "Cargo.lock", "why3find.json", "AGENTS.md", "crate/Cargo.toml",
        "crate/Cargo.toml.orig", "crate/.cargo_vcs_info.json",
        "scripts/verify.sh", "scripts/why3.conf", "scripts/check-proofs.py", "scripts/run-differential.sh",
        "verification/plan.md", "verification/specification.md",
        "verification/coverage.md", "verification/correspondence.md",
        "verification/public-api-inventory.md",
        "verification/assumptions.md", "verification/target-inventory.json",
        "verification/stdlib-model-design.md",
        "verification/probes/stdlib/Cargo.toml",
        "verification/probes/stdlib/Cargo.lock",
        "verification/probes/stdlib/src/lib.rs",
        "verification/provenance/README.md",
        "verification/provenance/form_urlencoded.sparse-index.jsonl",
        "verification/differential/Cargo.toml", "verification/differential/Cargo.lock",
        "verification/differential/src/main.rs",
        "verification/differential/upstream-copy/Cargo.toml",
        "verification/differential/upstream-copy/Cargo.toml.orig",
        "verification/differential/upstream-copy/Cargo.lock",
        "verification/differential/upstream-copy/.cargo_vcs_info.json",
        "capture/manifest.json", "capture/registry-metadata.json", "capture/release.crate",
        "capture/source/.cargo_vcs_info.json", "capture/source/Cargo.toml",
        "capture/source/Cargo.toml.orig",
    ):
        path = version / relative
        if path.is_file():
            paths.add(path)
    add_tree(paths, version / "crate/src", {".rs"})
    add_tree(paths, version / "capture/source/src", {".rs"})
    add_tree(paths, version / "verification/differential/upstream-copy/src", {".rs"})
    for relative in (
        "rust-toolchain.toml", "scripts/activate.sh", "scripts/activate-local.sh", "scripts/capture-crate-release.py",
        "scripts/audit-proof-evidence.py", ".agents/skills/creusot-verification/SKILL.md",
        "verification/playbook.md", "verification/templates/crate-plan.md",
    ):
        path = repo / relative
        if path.is_file():
            paths.add(path)

    metadata = subprocess.run(
        ["cargo", "metadata", "--offline", "--locked", "--format-version", "1",
         "--manifest-path", str(version / "Cargo.toml")],
        check=True, capture_output=True, text=True)
    packages = json.loads(metadata.stdout)["packages"]
    for name, revision in (("percent-encoding", "2.3.2"), ("creusot-std", "0.13.0"),
                           ("creusot-std-proc", "0.13.0")):
        matches = [p for p in packages if p["name"] == name and p["version"] == revision
                   and str(p.get("source", "")).startswith("registry+")]
        require(len(matches) == 1, f"Expected one locked registry package: {name} {revision}")
        dependency = Path(matches[0]["manifest_path"]).resolve().parent
        paths.add(dependency / "Cargo.toml")
        add_tree(paths, dependency / "src", {".rs"})

    xdg = Path(os.environ.get("XDG_DATA_HOME", "/workspace/.local/share"))
    config = xdg / "creusot/creusot_why3.conf"
    require(config.is_file(), f"Configured Creusot Why3 config missing: {config}")
    paths.add(config)
    package_root = xdg / "creusot/share/why3find/packages/creusot"
    require(package_root.is_dir() and any(package_root.rglob("*.coma")),
            f"Configured Creusot Why3 model package missing/empty: {package_root}")
    add_tree(paths, package_root)
    add_tree(paths, xdg / "creusot/_opam/share/why3/drivers")
    return sorted(paths)


def tool_hashes():
    tools = {}
    for name in ("cargo", "cargo-creusot", "cargo-proofs", "rustup", "why3find",
                 "why3", "alt-ergo", "z3", "cvc4", "cvc5"):
        executable = shutil.which(name)
        require(executable is not None, f"Required tool not on activated PATH: {name}")
        path = Path(executable).resolve()
        tools[name] = {"path": str(path), "sha256": digest(path)}
    creusot_rustc = Path(os.environ.get("XDG_DATA_HOME", "/workspace/.local/share")) / \
        "creusot/toolchains/nightly-2026-06-22/bin/creusot-rustc"
    require(creusot_rustc.is_file(), f"Creusot compiler wrapper missing: {creusot_rustc}")
    tools["creusot-rustc"] = {"path": str(creusot_rustc), "sha256": digest(creusot_rustc)}
    rustup = shutil.which("rustup")
    for label, channel in (("default", None), ("nightly-2026-06-22", "nightly-2026-06-22")):
        command = [rustup, "which", "rustc"] if channel is None else [
            rustup, "which", "--toolchain", channel, "rustc"]
        result = subprocess.run(command,
                                check=True, capture_output=True, text=True)
        path = Path(result.stdout.strip()).resolve()
        tools[f"rustc-{label}"] = {"path": str(path), "sha256": digest(path)}
    return tools


def snapshot(path):
    version = version_root()
    files = input_paths(version)
    record = {
        "created_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "inputs_sha256": {str(p.relative_to(version) if p.is_relative_to(version) else p): digest(p)
                          for p in files},
        "tools_sha256": tool_hashes(),
    }
    Path(path).write_text(json.dumps(record, indent=2) + "\n")
    print(f"Snapshotted {len(files)} input files and {len(record['tools_sha256'])} tools.")


def closed(tree):
    if not isinstance(tree, dict) or not tree:
        return False
    if "prover" in tree:
        return isinstance(tree["prover"], str) and bool(tree["prover"])
    if "tactic" in tree:
        children = tree.get("children")
        return (isinstance(tree["tactic"], str) and bool(tree["tactic"])
                and isinstance(children, list) and bool(children) and all(map(closed, children)))
    return all(isinstance(children, list) and bool(children) and all(map(closed, children))
               for children in tree.values())


def target_inventory(version):
    return json.loads((version / "verification/target-inventory.json").read_text())


def generated_root(run):
    return Path(run).resolve() / "coma/verif/form_urlencoded_rlib"


def selected_files(run):
    version = version_root()
    inventory = target_inventory(version)
    run = Path(run).resolve()
    root = generated_root(run)
    if not root.is_dir() and (run / "verif/form_urlencoded_rlib").is_dir():
        root = run / "verif/form_urlencoded_rlib"
    expected = set(inventory["selected"])
    for target in sorted(expected):
        path = root / f"{target}.coma"
        require(path.is_file(), f"Missing selected fresh Coma file: {path}")
        print(path.relative_to(version))


def package(run):
    version = version_root()
    run = Path(run).resolve()
    snapshot_path = run / "inputs-before.json"
    before = json.loads(snapshot_path.read_text())
    now = {str(p.relative_to(version) if p.is_relative_to(version) else p): digest(p)
           for p in input_paths(version)}
    require(now == before["inputs_sha256"], "Inputs changed during compile/proof; discard this run.")
    current_tools = tool_hashes()
    require(current_tools == before["tools_sha256"], "Tool binaries changed during compile/proof; discard this run.")
    after = {
        "created_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "inputs_sha256": now,
        "tools_sha256": current_tools,
    }
    (run / "inputs-after.json").write_text(json.dumps(after, indent=2) + "\n")
    require((run / "prove.exit").read_text().strip() == "0", "Why3find did not exit successfully")
    inventory = target_inventory(version)
    selected = inventory["selected"]
    opened = inventory.get("expected_open", {})
    excluded = inventory["excluded_generated"]
    require(not opened, "Expected-open targets are not supported by the final runner.")
    root = generated_root(run)
    generated_files = sorted(root.rglob("*.coma"))
    generated = {path.relative_to(root).as_posix().removesuffix(".coma"): path
                 for path in generated_files}
    classified = set(selected) | set(opened) | set(excluded)
    require(not (set(selected) & set(opened) or set(selected) & set(excluded)
                 or set(opened) & set(excluded)), "Target classifications overlap.")
    require(set(generated) == classified,
            f"Generated inventory mismatch: missing={sorted(classified - set(generated))}, "
            f"unclassified={sorted(set(generated) - classified)}")

    bundle = run / "bundle"
    bundle.mkdir(parents=True, exist_ok=True)
    sessions = {}
    total_goals = 0
    for target, rationale in selected.items():
        source = generated[target]
        proof = source.parent / target.rsplit("/", 1)[-1] / "proof.json"
        require(proof.is_file(), f"Missing fresh proof session: {target}")
        record = json.loads(proof.read_text())
        modules = record.get("proofs")
        require(isinstance(modules, dict) and bool(modules), f"No proof modules: {target}")
        goals = {f"{module}.{goal}": tree for module, group in modules.items()
                 for goal, tree in group.items()}
        require(goals and all(closed(tree) for tree in goals.values()),
                f"Unresolved root goal: {target}: {sorted(g for g, tree in goals.items() if not closed(tree))}")
        destination = bundle / target
        destination.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(proof, destination / "proof.json")
        shutil.copyfile(source, destination / "target.coma")
        sessions[target] = {
            "goals": len(goals),
            "proof_json_sha256": digest(destination / "proof.json"),
            "coma_sha256": digest(destination / "target.coma"),
            "open_goals": [],
            "goal_inventory": sorted(goals),
            "boundary": "Creusot/creusot-std models only",
            "contract": rationale,
        }
        total_goals += len(goals)

    versions = run / "versions.txt"
    differential_log = run / "differential/run.log"
    require(versions.is_file() and differential_log.is_file(),
            "Missing tool versions or native differential log.")
    summary = None
    for line in reversed(differential_log.read_text().splitlines()):
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if value.get("status") == "passed":
            summary = value
            break
    require(summary is not None, "No passing machine-readable differential summary.")
    expected_counts = {
        "singleton_inputs": 256,
        "pair_inputs": 65536,
        "alphabet_inputs": 19608,
        "random_inputs": 129,
        "targeted_escape_utf8_inputs": 13,
    }
    for field, expected in expected_counts.items():
        actual = summary.get(field)
        require(type(actual) is int and actual == expected,
                f"Unexpected differential {field}: expected {expected}, got {actual!r}")
    byte_input_total = sum(expected_counts[field] for field in (
        "singleton_inputs", "pair_inputs", "alphabet_inputs", "random_inputs"))
    total = byte_input_total + expected_counts["targeted_escape_utf8_inputs"]
    require(type(summary.get("byte_input_total")) is int
            and summary["byte_input_total"] == byte_input_total,
            f"Unexpected differential byte_input_total: expected {byte_input_total}, got {summary.get('byte_input_total')!r}")
    for field in ("owned_parse_inputs", "clone_after_next_inputs"):
        actual = summary.get(field)
        require(type(actual) is int and actual == total,
                f"Differential {field} must cover every byte input ({total}), got {actual!r}")
    require(type(summary.get("size_hint_step_observations")) is int
            and summary["size_hint_step_observations"] == 394459,
            "Unexpected differential size_hint_step_observations; inspect serializer coverage.")
    require(type(summary.get("serializer_chain_cases")) is int
            and summary["serializer_chain_cases"] == 1,
            "Unexpected serializer chain case count.")

    record = {
        "generated_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "scope": "Checked selected parser and byte-serializer proof targets. The finite native differential compares parser output and Cow borrowing, owned parsing, clone-after-next suffixes, every serializer chunk and size-hint step over 85,542 inputs, plus one serializer chain case.",
        "identity": "crates.io form_urlencoded 1.2.2 archive SHA-256 cb4cb245038516f5f85277875cdaa4f7d2c9a0fa0468de06ed190163b1581fcf; see verification/plan.md and provenance inputs.",
        "command": "bash scripts/verify.sh",
        "cache": False,
        "proof_command": "why3find prove --no-cache -f --summary --no-autodetect-provers -P z3,cvc5 -j 2 --fast 1 --time 10 -d 6 SELECTED_COMA_FILES",
        "why3_config": "scripts/why3.conf",
        "native_checks_sha256": {name: digest(run / "differential" / name) for name in ("tests.log", "check-alloc.log")},
        "log_sha256": {name: digest(run / name) for name in ("compile.log", "prove.log", "prove.exit")},
        "versions": versions.read_text().splitlines(),
        "versions_sha256": digest(versions),
        "tools_sha256": before["tools_sha256"],
        "inputs_sha256": before["inputs_sha256"],
        "targets": sessions,
        "total_session_goals": total_goals,
        "native_differential": {
            "command": "bash scripts/run-differential.sh RUN_DIRECTORY",
            "summary": summary,
            "log_sha256": digest(differential_log),
            "limits": "Finite observed correspondence only; not an all-input equivalence proof.",
        },
        "application_trusted_assumptions": [],
        "standard_library_assumptions": [
            "Creusot/creusot-std 0.13 integer, u8, slice and mutable-slice models.",
            "Reviewed standard-library content, ownership, and UTF-8 contracts in verification/assumptions.md.",
        ],
        "assumption_ledger": "verification/assumptions.md",
        "expected_open": {},
        "excluded_generated": excluded,
        "generated_target_count": len(generated),
        "goal_inventory_validation": "Fresh proof.json roots are recorded per target; audit reconstructs each complete root inventory from saved Coma with Why3.",
        "limitations": [
            "Serializer and EncodingOverride are excluded because the exact dynamic callback type cannot translate.",
            "Derived ByteSerialize Debug, individual standard-library default bodies, allocation/pointer identity, OOM, and all-platform behavior remain excluded.",
            "Finite differential observations do not prove upstream equivalence for all inputs.",
        ],
    }
    for filename in ("compile.log", "prove.log", "prove.exit", "versions.txt", "inputs-before.json", "inputs-after.json"):
        source = run / filename
        if source.is_file():
            shutil.copyfile(source, bundle / filename)
    for name in ("tests.log", "check-alloc.log"):
        shutil.copyfile(run / "differential" / name, bundle / name)
    shutil.copyfile(differential_log, bundle / "differential.log")
    (bundle / "manifest.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"bundle": str(bundle), "selected_targets": len(sessions),
                      "closed_root_goals": total_goals, "generated_target_count": len(generated),
                      "differential": summary}, indent=2))


def main():
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--snapshot", type=Path)
    group.add_argument("--selected-files", type=Path)
    group.add_argument("--package", type=Path)
    args = parser.parse_args()
    if args.snapshot:
        snapshot(args.snapshot)
    elif args.selected_files:
        selected_files(args.selected_files)
    else:
        package(args.package)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
