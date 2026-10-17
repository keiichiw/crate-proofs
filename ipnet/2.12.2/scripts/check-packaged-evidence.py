#!/usr/bin/env python3
"""Audit committed latest evidence without the ignored verifier work directory."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / "verification/evidence/latest"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    record = json.loads((PACKAGE / "package.json").read_text())
    assert record["status"] == "passed"
    for name, expected in record["files_sha256"].items():
        assert sha(PACKAGE / name) == expected, name
    original = json.loads((PACKAGE / "result.json").read_text())
    assert original["status"] == "passed"
    assert original["theorems"] == record["checked_theorems"]
    assert original["recorder_mappings"] == record["public_contract_mappings"]
    for name in record["files_sha256"]:
        if name != "result.json":
            assert original["files_sha256"].get(name) == record["files_sha256"][name] or name == "run.log", name
    assert (PACKAGE / "inputs-before.json").read_bytes() == (PACKAGE / "inputs-after.json").read_bytes()
    current = subprocess.check_output([sys.executable, str(ROOT / "scripts/fingerprint.py")], cwd=ROOT)
    assert json.loads(current) == json.loads((PACKAGE / "inputs-before.json").read_text()), "Current proof inputs differ"
    inventory = json.loads((ROOT / "verification/theorems.json").read_text())
    assert inventory["checked"] == original["theorems"]
    assert inventory["recorder_mappings"] == original["recorder_mappings"]
    # The full LLBC and generated model are omitted from this compact package.
    # The maintained model is the byte-compared output of the saved full run.
    assert sha(ROOT / "proofs/Ipnet.lean") == original["files_sha256"]["generated/Ipnet.lean"]
    omitted = sorted(set(original["files_sha256"]) - set(record["files_sha256"]))
    print(f"Packaged evidence PASS: {len(original['theorems'])} audited theorems, "
          f"{len(original['recorder_mappings'])} mappings, "
          f"{len(record['files_sha256'])} saved files, {len(omitted)} omitted working artifacts")


if __name__ == "__main__":
    main()
