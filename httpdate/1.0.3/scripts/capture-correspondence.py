#!/usr/bin/env python3
"""Bind a successful finite native comparison to its release and proof inputs."""
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile

VERSION = Path(__file__).resolve().parents[1]
BASE = VERSION / "verification/correspondence"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def formal_snapshot():
    spec = importlib.util.spec_from_file_location("formal_checker", VERSION / "scripts/check-proofs.py")
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    os.chdir(VERSION)
    manifest_path = VERSION / "verification/evidence/latest/manifest.json"
    formal = json.loads(manifest_path.read_text())
    current = checker.input_hashes()
    if current != formal["inputs_sha256"]:
        raise ValueError("Formal input fingerprints have changed; rerun verify.sh before binding")
    return {"formal_manifest_sha256": digest(manifest_path), "formal_inputs_sha256": current}


def native_snapshot():
    inputs = [BASE / "Cargo.toml", BASE / "Cargo.lock", BASE / "release.json",
              BASE / "registry-metadata.json", VERSION / "scripts/check-correspondence.sh",
              VERSION / "scripts/check-upstream-release.py", Path(__file__).resolve()]
    inputs += [VERSION / "Cargo.toml", VERSION / "Cargo.lock",
               VERSION / "crate/Cargo.toml", VERSION.parents[1] / "rust-toolchain.toml"]
    inputs += sorted((VERSION / "crate/src").rglob("*.rs"))
    inputs += sorted((BASE / "src").rglob("*.rs"))
    inputs += sorted(p for p in (BASE / "reference").rglob("*") if p.is_file())
    # These four complete runtime function texts are byte-identical, not merely
    # normalized by a comment/attribute-stripping heuristic.
    source = (VERSION / "crate/src/date.rs").read_text()
    reference = (BASE / "reference/src/date.rs").read_text()
    unchanged = {}
    for name in ("toint_1", "toint_2", "toint_4", "is_leap_year"):
        pattern = rf"(?ms)^fn {name}\(.*?^\}}"
        a = re.findall(pattern, source)
        b = re.findall(pattern, reference)
        if len(a) != 1 or a != b:
            raise ValueError(f"Unchanged runtime-function correspondence failed: {name}")
        unchanged[name] = hashlib.sha256(a[0].encode()).hexdigest()
    return {
        "correspondence_inputs_sha256": {os.path.relpath(p, VERSION): digest(p) for p in inputs},
        "byte_identical_runtime_functions_sha256": unchanged,
    }


ARTIFACTS = ("result.json", "build.log", "release-check.log", "release-check-arguments.json")


def main():
    if sys.argv[1:] == ["--snapshot"]:
        print(json.dumps(native_snapshot(), indent=2))
        return
    bind = len(sys.argv) == 3 and sys.argv[1] == "--bind"
    if not bind and len(sys.argv) != 2:
        raise ValueError("usage: capture-correspondence.py --snapshot | RUN_DIRECTORY | --bind RUN_DIRECTORY")
    run = Path(sys.argv[-1]).resolve()
    captured = json.loads((run / "inputs.json").read_text())
    if captured != native_snapshot():
        raise ValueError("Comparison inputs changed; rerun the native comparison")
    if bind:
        native = json.loads((run / "native-manifest.json").read_text())
        if native["correspondence_inputs_sha256"] != captured["correspondence_inputs_sha256"]:
            raise ValueError("Native manifest does not match captured inputs")
        if native["artifacts_sha256"] != {name: digest(run / name) for name in ARTIFACTS}:
            raise ValueError("Native artifacts changed since comparison completion")
        formal = formal_snapshot()
    result = json.loads((run / "result.json").read_text())
    expected = {"status", "civil_days", "boundary_instants", "parser_inputs", "trait_pairs",
                "formatting_observations", "writer_observations", "panic_observations",
                "error_observations", "seed"}
    if set(result) != expected or result["status"] != "passed":
        raise ValueError("Comparison did not report a complete successful result")
    for key in expected - {"status", "seed"}:
        if not isinstance(result[key], int) or result[key] <= 0:
            raise ValueError(f"Missing native comparison observations: {key}")
    if result["civil_days"] != 253402300800 // 86400:
        raise ValueError("Not every supported civil day was compared")
    version = (native["rustc"] if bind else
               subprocess.check_output(["rustc", "-Vv"], text=True).splitlines())
    record = {
        "schema_version": 2,
        "mode": "formal-bound" if bind else "native-only",
        "generated_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "scope": "Finite native observations against byte-unchanged crates.io 1.0.3 runtime sources; not formal semantic equivalence",
        "command": "bash httpdate/1.0.3/scripts/check-correspondence.sh",
        "release_check_arguments": json.loads((run / "release-check-arguments.json").read_text()),
        "host": native["host"] if bind else {"system": platform.system(), "machine": platform.machine()},
        "rustc": version,
        "proof_source_baseline_commit": "42c3027836b797e8acc1bc4cd199873f8bd6f169",
        "result": result,
        **captured,
        **(formal if bind else {}),
        "artifacts_sha256": {name: digest(run / name) for name in ARTIFACTS},
    }
    if not bind:
        (run / "native-manifest.json").write_text(json.dumps(record, indent=2) + "\n")
        print(f"Saved standalone native result: {run / 'native-manifest.json'}")
        return
    if native["result"] != result:
        raise ValueError("Native result differs from its completed manifest")
    record["native_manifest_sha256"] = digest(run / "native-manifest.json")
    (run / "manifest.json").write_text(json.dumps(record, indent=2) + "\n")
    latest = BASE / "evidence/latest"
    latest.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix=".capture-", dir=latest.parent))
    try:
        for name in ("manifest.json", "native-manifest.json", "inputs.json", *ARTIFACTS):
            shutil.copyfile(run / name, temporary / name)
        # Check once more before replacing the saved observations.
        if captured != native_snapshot() or formal != formal_snapshot():
            raise ValueError("Comparison inputs changed before evidence replacement")
        if latest.exists():
            latest.rename(latest.parent / ("historical-" + temporary.name.removeprefix(".capture-")))
        temporary.rename(latest)
    finally:
        if temporary.exists():
            shutil.rmtree(temporary)
    print(f"Saved native correspondence evidence: {latest.relative_to(VERSION)}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
