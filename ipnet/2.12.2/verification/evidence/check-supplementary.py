#!/usr/bin/env python3
"""Check committed candidate, bug, tool-repro and blocker evidence hashes."""
import hashlib
import json
from pathlib import Path

VERSION = Path(__file__).resolve().parents[2]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


def check(base, manifest, key="files_sha256", file_root=None):
    base = VERSION / base
    data = json.loads((base / manifest).read_text())
    root = base if file_root is None else VERSION / file_root
    for name, expected in data[key].items():
        assert sha(root / name) == expected, f"{base / name}: stale or absent"
    print(f"{base.relative_to(VERSION)}: {len(data[key])} hashes PASS")


def main():
    check("verification/heapless-candidate/evidence/latest", "result.json")
    check("verification/bugs/schema-repro", "evidence.json")
    check("verification/bugs/heapless-feature-repro", "evidence.json")
    check("verification/bugs/heapless-feature-repro", "ipv6-evidence.json")
    check("verification/bugs/subnets-domain-repro", "evidence.json")
    check("verification/issue-repros/ipnet", "evidence.json", "sha256", file_root=".")
    check("verification/issue-repros/aeneas", "evidence.json", file_root="verification/issue-repros/aeneas/evidence/latest")
    check("verification/blockers/aggregate-extend", "evidence.json")
    check("verification/blockers/ipv4-parser-callback", "evidence.json")
    print("Supplementary evidence PASS; these checks do not prove Rust behavior")


if __name__ == "__main__":
    main()
