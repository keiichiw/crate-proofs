#!/usr/bin/env python3
"""Regenerate committed native counterexample logs from unchanged release source."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
VERSION = ROOT.parents[1]
RUN = Path(tempfile.mkdtemp(prefix="bugs-refresh-", dir=VERSION / "verification/runs"))
ENV = os.environ.copy()
ENV["CARGO_TARGET_DIR"] = str(RUN / "target")
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


def execute(name, args, stdout, stderr, expected=0):
    p = subprocess.run([str(a) for a in args], cwd=VERSION, env=ENV,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout.write_bytes(p.stdout)
    stderr.write_bytes(p.stderr)
    assert p.returncode == expected, f"{name} exit {p.returncode} != {expected}: {stderr}"
    print(name, p.returncode, flush=True)
    return p


def main():
    schema = ROOT / "schema-repro"
    execute("schema-generate", ["cargo", "+1.91.1", "run", "--offline", "--locked",
            "--manifest-path", schema / "Cargo.toml"], schema / "generated.json",
            schema / "generate.log")
    python = VERSION / ".tools/schema-python/bin/python"
    assert python.is_file(), "Pinned jsonschema environment missing; run target setup"
    execute("schema-check", [python, schema / "check.py"], schema / "result.json",
            schema / "check.log")
    # This command is supposed to fail on the known output-conformance defect.
    p = subprocess.run([str(python), str(schema / "check.py"), "--expect-fixed"],
                       cwd=VERSION, env=ENV, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    assert p.returncode != 0 and b"Output conformance violated" in p.stdout
    (schema / "expected-failing-regression.log").write_bytes(p.stdout)
    schema_files = ["Cargo.toml", "Cargo.lock", "check.py", "requirements.txt",
                    "src/main.rs", "generated.json", "result.json", "generate.log",
                    "check.log", "expected-failing-regression.log"]
    (schema / "evidence.json").write_text(json.dumps({
        "status": "counterexamples reproduced; regression assertion expectedly fails",
        "fresh_run": RUN.name,
        "files_sha256": {n: sha(schema / n) for n in schema_files},
    }, indent=2) + "\n")

    heap = ROOT / "heapless-feature-repro"
    logs = []
    for name, features, binary in [("heapless", "heapless", None),
                                    ("legacy", "legacy", None),
                                    ("ipv6-heapless", "heapless", "ipv6"),
                                    ("ipv6-legacy", "legacy", "ipv6")]:
        cmd = ["cargo", "+1.91.1", "run", "--offline", "--locked",
               "--manifest-path", heap / "Cargo.toml", "--features", features]
        if binary:
            cmd.extend(["--bin", binary])
        log = heap / f"{name}.log"
        err = RUN / f"{name}.stderr"
        execute(name, cmd, log, err)
        logs.append(name + ".log")
    v4_heap = (heap / "heapless.log").read_text()
    v4_legacy = (heap / "legacy.log").read_text()
    v6_heap = (heap / "ipv6-heapless.log").read_text()
    v6_legacy = (heap / "ipv6-legacy.log").read_text()
    assert "allocations=3" in v4_heap and "allocations=0" in v4_legacy
    assert "allocations=4" in v6_heap and "allocations=0" in v6_legacy
    files = ["Cargo.toml", "Cargo.lock", "src/main.rs", "src/bin/ipv6.rs", *logs]
    common = {"fresh_run": RUN.name, "status": "native allocation counterexample",
              "files_sha256": {n: sha(heap / n) for n in files}}
    (heap / "evidence.json").write_text(json.dumps(common, indent=2) + "\n")
    (heap / "ipv6-evidence.json").write_text(json.dumps({
        **common, "scope": "IPv6 extension of the same IPNET-003 finding",
    }, indent=2) + "\n")

    subnet = ROOT / "subnets-domain-repro"
    execute("subnets-domain", ["cargo", "+1.91.1", "run", "--offline", "--locked",
            "--manifest-path", subnet / "Cargo.toml"], subnet / "observed.log",
            subnet / "build.log")
    observed = (subnet / "observed.log").read_text()
    assert "q=33" in observed and "q=255" in observed and "Ok(None)" in observed
    (subnet / "evidence.json").write_text(json.dumps({
        "fresh_run": RUN.name,
        "classification": "known invalid-prefix raw-state behavior, not new bug",
        "files_sha256": {n: sha(subnet / n) for n in
                         ["Cargo.toml", "Cargo.lock", "src/main.rs", "observed.log", "build.log"]},
    }, indent=2) + "\n")
    print(f"Native findings refreshed: {RUN}")


if __name__ == "__main__":
    main()
