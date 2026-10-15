#!/usr/bin/env python3
"""Export every fresh probe root and check every generated SMT-LIB goal with Z3."""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import subprocess
import sys


def run(command: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, cwd=cwd, text=True, capture_output=True, check=False)


def main() -> int:
    if len(sys.argv) != 3:
        print("usage: check_roots.py FRESH_COMA OUTPUT_DIR", file=sys.stderr)
        return 2
    coma = Path(sys.argv[1]).resolve()
    output = Path(sys.argv[2]).resolve()
    cwd = Path.cwd()
    output.mkdir(parents=True, exist_ok=False)
    xdg = Path(os.environ["XDG_DATA_HOME"])
    config = xdg / "creusot/creusot_why3.conf"
    library = xdg / "creusot/share/why3find/packages/creusot"
    base = ["why3", "prove", "-C", str(config), "-L", str(library), str(coma)]

    listing = run(base, cwd)
    (output / "roots.stdout.txt").write_text(listing.stdout)
    (output / "roots.stderr.txt").write_text(listing.stderr)
    if listing.returncode != 0:
        print(json.dumps({"status": "failed", "stage": "root-listing", "exit_code": listing.returncode}))
        return 1

    roots: list[tuple[str, str, bool]] = []
    theory: str | None = None
    for line in listing.stdout.splitlines():
        mt = re.match(r"^theory (\S+)$", line)
        if mt:
            theory = mt.group(1)
            continue
        mg = re.match(r"^\s+goal (\S+)\s*:\s*(.*)$", line)
        if mg:
            if theory is None:
                print("goal encountered before its theory", file=sys.stderr)
                return 1
            roots.append((theory, mg.group(1), mg.group(2).strip() == "true"))
    if not roots:
        print(json.dumps({"status": "failed", "stage": "root-listing", "reason": "no roots"}))
        return 1

    results = []
    all_closed = True
    z3_timeout = int(os.environ.get("PROBE_Z3_TIMEOUT", "5"))
    for index, (theory, goal, is_true_root) in enumerate(roots):
        root_dir = output / f"{index:03d}-{goal}"
        transformed = root_dir / "transformed"
        transformed.mkdir(parents=True)
        cmd = base + ["-T", theory, "-G", goal, "-a", "compute_specified", "-a", "split_vc", "-P", "Z3", "-o", str(transformed)]
        exported = run(cmd, cwd)
        (root_dir / "transformed.stdout.txt").write_text(exported.stdout)
        (root_dir / "transformed.stderr.txt").write_text(exported.stderr)
        smt_files = sorted(transformed.rglob("*.smt2"))
        mode = "transformed"

        if exported.returncode != 0:
            all_closed = False
            results.append({"goal": f"{theory}.{goal}", "status": "export-failed", "exit_code": exported.returncode})
            continue

        if not smt_files:
            raw = root_dir / "untransformed"
            raw.mkdir()
            raw_cmd = base + ["-T", theory, "-G", goal, "-P", "Z3", "-o", str(raw)]
            raw_export = run(raw_cmd, cwd)
            (root_dir / "untransformed.stdout.txt").write_text(raw_export.stdout)
            (root_dir / "untransformed.stderr.txt").write_text(raw_export.stderr)
            if raw_export.returncode != 0:
                all_closed = False
                results.append({"goal": f"{theory}.{goal}", "status": "untransformed-export-failed", "exit_code": raw_export.returncode})
                continue
            smt_files = sorted(raw.rglob("*.smt2"))
            mode = "untransformed"

        if not smt_files:
            closed = is_true_root
            if not closed:
                all_closed = False
            results.append({"goal": f"{theory}.{goal}", "status": "true-root-eliminated" if closed else "no-smt-export", "smt_files": 0, "export_mode": mode})
            continue

        smt_results = []
        for smt in smt_files:
            z3_command = ["z3", "-smt2", f"-T:{z3_timeout}", "sat.random_seed=42", "nlsat.randomize=false", "smt.random_seed=42", str(smt)]
            checked = run(z3_command, cwd)
            (root_dir / f"{smt.stem}.z3.stdout.txt").write_text(checked.stdout)
            (root_dir / f"{smt.stem}.z3.stderr.txt").write_text(checked.stderr)
            statuses = [line.strip() for line in checked.stdout.splitlines() if line.strip() in {"sat", "unsat", "unknown", "timeout"}]
            passed = checked.returncode == 0 and statuses == ["unsat"] and "(error" not in checked.stdout.lower()
            smt_results.append({"file": str(smt.relative_to(output)), "exit_code": checked.returncode, "statuses": statuses, "passed": passed})
            all_closed = all_closed and passed
        results.append({"goal": f"{theory}.{goal}", "status": "closed" if all(item["passed"] for item in smt_results) else "open", "export_mode": mode, "smt_results": smt_results})

    summary = {"status": "passed" if all_closed else "failed", "root_count": len(roots), "direct_smt_goals": sum(len(r.get("smt_results", [])) for r in results), "results": results}
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, separators=(",", ":")))
    return 0 if all_closed else 1


if __name__ == "__main__":
    raise SystemExit(main())
