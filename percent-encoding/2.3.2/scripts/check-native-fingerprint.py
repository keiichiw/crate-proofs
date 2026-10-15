#!/usr/bin/env python3
"""Check native run fingerprints against the verification input snapshot."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys


def fail(message: str) -> None:
    raise ValueError(message)


def parse_section(lines: list[str], marker: str) -> dict[str, str]:
    try:
        start = lines.index(marker) + 1
        end = next((i for i in range(start, len(lines)) if lines[i] in {"BEFORE", "AFTER"}), len(lines))
    except ValueError:
        fail(f"native fingerprint lacks {marker} section")
    rows: dict[str, str] = {}
    for line in lines[start:end]:
        if not line.strip():
            continue
        parts = line.split(None, 1)
        if len(parts) != 2 or len(parts[0]) != 64:
            fail(f"malformed native fingerprint row: {line!r}")
        digest, name = parts
        if name in rows:
            fail(f"duplicate native fingerprint path: {name}")
        rows[name] = digest
    if not rows:
        fail(f"empty native fingerprint section: {marker}")
    return rows


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--fingerprint", type=Path, required=True)
    ap.add_argument("--snapshot", type=Path, required=True)
    ap.add_argument("--repo-root", type=Path, required=True)
    ap.add_argument("--version-dir", type=Path, required=True)
    ap.add_argument("--run-id", required=True)
    args = ap.parse_args()
    lines = args.fingerprint.read_text().splitlines()
    expected_id = f"RUN_ID={args.run_id}"
    if not lines or lines[0] != expected_id:
        fail("native fingerprint run ID mismatch")
    if not args.run_id.startswith("percent-encoding-2.3.2-full-scope-"):
        fail("native fingerprint run ID is not unique full-scope identity")
    before = parse_section(lines, "BEFORE")
    after = parse_section(lines, "AFTER")
    if before != after:
        fail("native source/config fingerprint changed during native checks")
    snapshot = json.loads(args.snapshot.read_text()).get("inputs_sha256", {})
    repo_root = args.repo_root.resolve()
    version_dir = args.version_dir.resolve()
    for rel, digest in before.items():
        path = (repo_root / rel).resolve()
        key = str(path.relative_to(version_dir)) if path.is_relative_to(version_dir) else str(path)
        if snapshot.get(key) != digest:
            fail(f"native fingerprint does not match final-run input snapshot: {rel}")
    paths = set(before)
    required = {
        "crate/Cargo.toml", "crate/Cargo.lock",
        "verification/differential/Cargo.toml",
        "verification/differential/Cargo.lock",
        "verification/differential/src/main.rs",
        "verification/differential/run-full-scope.sh",
        "verification/differential/upstream-copy/Cargo.toml",
        "verification/differential/upstream-copy/Cargo.lock",
    }
    # Native manifests use repository-root-relative paths.
    relative_version = version_dir.relative_to(repo_root).as_posix()
    required = {f"{relative_version}/{p}" for p in required}
    for root in (version_dir / "crate/src",
                 version_dir / "verification/differential/src",
                 version_dir / "verification/differential/upstream-copy/src",
                 version_dir / "capture/source"):
        if root.is_dir():
            required.update((root / p).relative_to(repo_root).as_posix()
                            for p in root.rglob("*") if p.is_file())
    if not required.issubset(paths):
        fail("native fingerprint omits required crate/harness inputs: "
             + ", ".join(sorted(required - paths)))
    print(json.dumps({"status": "passed", "run_id": args.run_id,
                      "fingerprinted_files": len(before),
                      "input_snapshot_matches": True}, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
