#!/usr/bin/env python3
"""Validate conditional boundary proofs separately from httpdate evidence."""
import datetime
import hashlib
import json
from pathlib import Path
import runpy
import shutil
import sys

TARGETS = ("bounded_epoch_seconds", "epoch_time", "time_boundary_roundtrip",
           "ascii_text", "normalized_ascii")
VERSION = Path(__file__).resolve().parents[3]
CHECKER = VERSION / "scripts/check-proofs.py"
proved = runpy.run_path(str(CHECKER))["proved"]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inputs():
    files = [Path(p) for p in ("Cargo.toml", "Cargo.lock", "src/lib.rs", "why3find.json",
                               "run.sh", "check.py", "README.md", "reference/manifest.json")]
    files += [CHECKER, VERSION.parents[1] / "scripts/activate.sh",
              VERSION.parents[1] / "rust-toolchain.toml"]
    return {str(path): digest(path) for path in files}


def main():
    if sys.argv[1:] == ["--snapshot"]:
        print(json.dumps(inputs(), indent=2))
        return
    run = Path(sys.argv[1])
    captured = json.loads((run / "inputs.json").read_text())
    if inputs() != captured:
        raise ValueError("Inputs changed while proving; run again.")
    base = run / "coma/verif/httpdate_boundary_model_rlib"
    sessions = {}
    for target in TARGETS:
        proof = base / target / "proof.json"
        modules = json.loads(proof.read_text()).get("proofs", {})
        goals = {f"{module}.{goal}": tree for module, group in modules.items()
                 for goal, tree in group.items()}
        if not goals or not any(goal.endswith(f".vc_{target}") for goal in goals):
            raise ValueError(f"No target VC: {target}")
        if not all(map(proved, goals.values())):
            raise ValueError(f"Unproved session: {target}")
        sessions[target] = {"session_goals": len(goals), "proof_json_sha256": digest(proof),
                            "coma_sha256": digest(base / f"{target}.coma")}
    summary = {
        "generated_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "scope": "Conditional proofs in an isolated candidate-model crate; not public httpdate API proofs or stdlib implementation verification.",
        "target_platform": "64-bit Linux",
        "trusted_assumptions_review": "README.md",
        "input_sha256": captured,
        "versions": (run / "versions.txt").read_text().splitlines(),
        "targets": sessions,
        "total_session_goals": sum(item["session_goals"] for item in sessions.values()),
        "cache": False,
        "native_tests": "cargo test --locked: three sanity-check tests (see tests.log)",
        "command": "bash httpdate/1.0.3/verification/trial/boundary-model/run.sh",
    }
    output = Path("evidence/latest")
    output.mkdir(parents=True, exist_ok=True)
    for target in TARGETS:
        dest = output / target
        dest.mkdir(exist_ok=True)
        shutil.copyfile(base / target / "proof.json", dest / "proof.json")
        shutil.copyfile(base / f"{target}.coma", dest / "target.coma")
    for log in ("tests.log", "compile.log", "prove.log", "versions.txt"):
        shutil.copyfile(run / log, output / log)
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(f"Conditional boundary proofs: {len(TARGETS)} targets, {summary['total_session_goals']} session goals.")


if __name__ == "__main__":
    main()
