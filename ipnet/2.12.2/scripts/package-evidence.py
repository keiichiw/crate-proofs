#!/usr/bin/env python3
"""Preserve the selected output of a fresh successful local verifier run.

The verifier's large working directory stays ignored. This checks its hashes
before copying the logs needed to review the accepted scope into maintained
evidence/latest. Historical run directories are not repackaged by this tool.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("run", type=Path, help="Fresh run from scripts/verify.sh")
    args = parser.parse_args()
    run = args.run.resolve()
    assert run.parent == (ROOT / "verification/runs").resolve()
    result = json.loads((run / "result.json").read_text())
    assert result["status"] == "passed"
    assert (run / "inputs-before.json").read_bytes() == (run / "inputs-after.json").read_bytes()
    for rel, expected in result["files_sha256"].items():
        assert sha(run / rel) == expected, rel

    selected = [
        "result.json", "inputs-before.json", "inputs-after.json", "run.log",
        "native-default.log", "native-no-std.log", "native-all-features.log",
        "shift-model-checks.log",
        "lean-clean.log", "generated/charon.log", "generated/aeneas.log",
        "generated/extraction.json", "audit/result.json", "audit/build.log",
    ]
    selected += sorted(str(p.relative_to(run)) for p in (run / "audit").glob("audit*.log"))
    destination = ROOT / "verification/evidence/latest"
    staging = ROOT / "verification/evidence/.stage"
    if staging.exists():
        shutil.rmtree(staging)
    staging.mkdir(parents=True)
    for name in selected:
        source = run / name
        assert source.is_file(), name
        target = staging / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
    metadata = {
        "source_run": run.name,
        "status": "passed",
        "checked_theorems": result["theorems"],
        "public_contract_mappings": result["recorder_mappings"],
        "scope": result["scope"],
        "files_sha256": {name: sha(staging / name) for name in selected},
    }
    (staging / "package.json").write_text(json.dumps(metadata, indent=2) + "\n")
    if destination.exists():
        shutil.rmtree(destination)
    staging.rename(destination)
    print(destination)


if __name__ == "__main__":
    main()
