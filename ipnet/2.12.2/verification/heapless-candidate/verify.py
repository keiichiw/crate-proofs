#!/usr/bin/env python3
"""Fresh, offline candidate checks; package selected evidence outside ignored runs.

This validates source provenance and finite/conditional checks. Expected Aeneas
failures are evidence of a translation boundary, not application-body proofs.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
VERSION = ROOT.parents[1]
REPO = VERSION.parents[1]
EVIDENCE = ROOT / "evidence" / "latest"
RUNS = ROOT / "runs"
RUNS.mkdir(exist_ok=True)
RUN = Path(tempfile.mkdtemp(prefix="check-", dir=RUNS))
ENV = os.environ.copy()
ENV["CARGO_TARGET_DIR"] = str(RUN / "target")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(label, argv, cwd=ROOT, expect=0):
    result = subprocess.run([str(a) for a in argv], cwd=cwd, env=ENV,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = RUN / f"{label}.log"
    log.write_bytes(result.stdout)
    if expect is not None and result.returncode != expect:
        raise RuntimeError(f"{label} exited {result.returncode}, expected {expect}: {log}")
    print(f"{label}: exit {result.returncode}", flush=True)
    return result, log


def extract(label, selector):
    out = RUN / label
    out.mkdir()
    llbc = out / "candidate.llbc"
    command(f"{label}-charon", ["charon", "cargo", "--preset=aeneas",
            "--start-from", selector, "--dest-file", llbc, "--",
            "--features", "heapless", "--lib", "--locked"])
    result, log = command(f"{label}-aeneas",
                          ["aeneas", "-backend", "lean", "-dest", out, llbc],
                          expect=None)
    if result.returncode == 0 or b"Unsupported cast to a dynamic trait" not in log.read_bytes():
        raise RuntimeError(f"{label} did not reproduce the mutable dyn cast boundary: {log}")
    return result.returncode


def main():
    command("source", ["python3", ROOT / "check-source.py"])
    command("tools", ["python3", VERSION / "scripts/check-tools.py"])
    command("candidate-tests", ["cargo", "+1.91.1", "test", "--offline", "--locked",
            "--manifest-path", ROOT / "Cargo.toml", "--features", "heapless"])
    command("legacy-no-default-check", ["cargo", "+1.91.1", "check", "--offline",
            "--locked", "--manifest-path", ROOT / "Cargo.toml",
            "--no-default-features", "--features", "ser_as_str"])
    math = ROOT / "proofs/CapacityMath.lean"
    command("capacity-lean", ["lake", "env", "lean", math], VERSION / "proofs")
    names = [x["name"] for x in json.loads((ROOT / "proofs/audit.json").read_text())["checked"]]
    assert len(names) == 22
    audit = RUN / "CapacityMathAudit.lean"
    audit.write_text(math.read_text() + "\n" + "\n".join(f"#print axioms {n}" for n in names) + "\n")
    _, audit_log = command("capacity-axioms", ["lake", "env", "lean", audit], VERSION / "proofs")
    axiom_lines = re.findall(r"^'{0,1}[^\n]*' depends on axioms: \[([^\]]*)\]", audit_log.read_text(), re.M)
    if len(axiom_lines) != 22:
        raise RuntimeError(f"Expected 22 axiom audit lines: {audit_log}")
    permitted = {"propext", "Classical.choice", "Quot.sound"}
    for line in axiom_lines:
        found = {x.strip() for x in line.split(",") if x.strip()}
        if not found <= permitted:
            raise RuntimeError(f"Unexpected axiom {found - permitted}: {audit_log}")
    command("native-matrix", ["python3", ROOT / "native/check.py"])
    outcomes = {}
    for label, selector in {
        "ipv4-serialize": "{impl serde_core::ser::Serialize for crate::ipnet::Ipv4Net}::serialize",
        "ipv6-serialize": "{impl serde_core::ser::Serialize for crate::ipnet::Ipv6Net}::serialize",
        "ipnet-serialize": "{impl serde_core::ser::Serialize for crate::ipnet::IpNet}::serialize",
    }.items():
        outcomes[label] = extract(label, selector)

    # The latest directory is replaced only after every required check succeeds.
    staged = ROOT / "evidence" / (".stage-" + RUN.name)
    staged.mkdir(parents=True)
    keep = ["source.log", "tools.log", "candidate-tests.log",
            "legacy-no-default-check.log", "capacity-lean.log", "capacity-axioms.log",
            "native-matrix.log"]
    keep += [f"{label}-{stage}.log" for label in outcomes for stage in ("charon", "aeneas")]
    for name in keep:
        shutil.copy2(RUN / name, staged / name)
    matrix_path = Path((RUN / "native-matrix.log").read_text().strip().splitlines()[-1])
    if not matrix_path.is_absolute() or not (matrix_path / "native-result.json").is_file():
        raise RuntimeError("native matrix did not report its result directory")
    shutil.copy2(matrix_path / "native-result.json", staged / "native-result.json")
    native = json.loads((staged / "native-result.json").read_text())
    if len(native["results"]) != 10 or any(x["exit_code"] for x in native["results"]):
        raise RuntimeError("Expected ten passing native feature combinations")
    for item in native["results"]:
        shutil.copy2(matrix_path / item["log"], staged / item["log"])
    result = {
        "status": "conditional-helpers-and-finite-native-pass; actual-serialize-extraction-blocked",
        "theorems": 22,
        "native_feature_combinations": 10,
        "native_cases_per_combination": 6216,
        "expected_aeneas_failure_exit_codes": outcomes,
        "not_proved": "Actual ipnet Serialize and Display body contracts",
        "source_sha256": digest(math),
        "candidate_patch_sha256": digest(ROOT / "cfg.patch"),
        "pinned_toolchain_sha256": digest(VERSION / "verification/toolchain.json"),
        "files_sha256": {name: digest(staged / name) for name in sorted(p.name for p in staged.iterdir())},
    }
    (staged / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    audit_record = json.loads((ROOT / "proofs/audit.json").read_text())
    audit_record["source_sha256"] = digest(math)
    audit_record["audit_log_sha256"] = digest(audit_log)
    audit_record["fresh_evidence"] = "evidence/latest/capacity-axioms.log"
    (ROOT / "proofs/audit.json").write_text(json.dumps(audit_record, indent=2) + "\n")
    if EVIDENCE.exists():
        shutil.rmtree(EVIDENCE)
    staged.rename(EVIDENCE)
    print(f"candidate evidence: {EVIDENCE}")


if __name__ == "__main__":
    main()
