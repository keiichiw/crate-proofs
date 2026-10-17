#!/usr/bin/env python3
"""Check the saved local evidence without reading ignored verification/runs/."""

import argparse
import hashlib
import json
import re
from pathlib import Path


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path, help="saved check-* evidence directory")
    args = parser.parse_args()
    package = args.package.resolve()
    root = Path(__file__).resolve().parents[2]

    manifest = json.loads((package / "manifest.json").read_text())
    entries = manifest["files"]
    require(len(entries) == len({entry["path"] for entry in entries}), "duplicate evidence path")
    for entry in entries:
        relative = Path(entry["path"])
        require(not relative.is_absolute() and ".." not in relative.parts,
                f"unsafe evidence path: {relative}")
        path = package / relative
        require(path.is_file(), f"missing evidence file: {relative}")
        require(path.stat().st_size == entry["bytes"], f"size mismatch: {relative}")
        require(sha256(path) == entry["sha256"], f"hash mismatch: {relative}")

    require(sha256(package / "result.json") == manifest["accepted_result_sha256"],
            "accepted result hash mismatch")
    result = json.loads((package / "result.json").read_text())
    require(result["status"] == "passed", "run did not pass")
    for relative, expected in result["files_sha256"].items():
        require(sha256(package / relative) == expected,
                f"result-internal hash mismatch: {relative}")
    require((package / "inputs-before.json").read_bytes() ==
            (package / "inputs-after.json").read_bytes(),
            "before/after input fingerprints differ")
    require((package / "generated/Adler2.lean").read_bytes() ==
            (root / "proofs/Adler2.lean").read_bytes(),
            "saved extraction differs from maintained generated model")

    inventory = json.loads((root / "verification/theorems.json").read_text())
    require(result["theorems"] == inventory["checked"], "theorem inventory differs")
    require(result["recorder_mappings"] == inventory["recorder_mappings"],
            "recorder mappings differ")
    expected = [entry["name"] for entry in inventory["checked"]]
    audited = re.findall(r"^AUDIT OK: ([A-Za-z_][A-Za-z_0-9.]*)\b;",
                         (package / "lean-audit.log").read_text(), re.M)
    require(audited == expected, "theorem audit list differs")
    mapped = [entry["theorem"] for entry in inventory["recorder_mappings"]]
    recorded = re.findall(r"^proofs\.rs:checked:([A-Za-z_][A-Za-z_0-9.]*)$",
                          (package / "recorder-audit.log").read_text(), re.M)
    require(recorded == mapped, "recorder audit list differs")

    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for line in (package / "lean-audit.log").read_text().splitlines():
        if not line.startswith("AUDIT OK: "):
            continue
        match = re.search(r"axioms: \[([^]]*)\]$", line)
        require(match is not None, f"missing axiom listing: {line}")
        axioms = {item.strip() for item in match.group(1).split(",") if item.strip()}
        require(axioms <= allowed, f"unapproved axiom listing: {line}")

    print(f"Saved evidence OK: {len(entries)} files, {len(expected)} theorem roots, "
          f"{len(mapped)} mapped APIs")
    print(f"Result SHA-256: {manifest['accepted_result_sha256']}")


if __name__ == "__main__":
    main()
