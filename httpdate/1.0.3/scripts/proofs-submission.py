#!/usr/bin/env python3
"""Check four API proofs locally, or record them using an installed cargo-proofs.

Activate the verification environment first. No mode logs in, pushes, or publishes.
The supporting full-suite archive is audited separately from the fresh API run.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import tempfile
import tomllib
import uuid

VERSION = Path(__file__).resolve().parents[1]
REPO = VERSION.parents[1]
BASELINE = VERSION / "verification/evidence/httpdate-run-Nh8aCaki/manifest.json"
BASELINE_SHA = "528cb7465e8de245d8509e6fcb5c21cb87a2396015faacf7c4c0bd0ee06192d0"
TARGETS = {
    "parse_http_date": "crate/src/lib.rs",
    "fmt_http_date": "crate/src/lib.rs",
    "date/impl_FromStr_for_HttpDate/from_str": "crate/src/date.rs",
    "date/impl_Display_for_HttpDate/fmt": "crate/src/date.rs",
}
APIS = {
    "httpdate::parse_http_date",
    "httpdate::fmt_http_date",
    "<httpdate::HttpDate as std::str::FromStr>::from_str",
    "<httpdate::HttpDate as std::fmt::Display>::fmt",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def checker():
    spec = importlib.util.spec_from_file_location("httpdate_proofs", VERSION / "scripts/check-proofs.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def command(output):
    base = output / "verif/httpdate_rlib"
    return [
        "cargo", "creusot", "-p", "httpdate", "--span-mode", "absolute",
        "--output-dir", str(output), "--no-cache",
        "--why3find-arg=--prover=-cvc4,-cvc5", "--why3find-arg=-j", "--why3find-arg=2",
        "--why3find-arg=--fast=1", "--why3find-arg=--time=10",
        "--why3find-arg=-d", "--why3find-arg=2",
        *(str(base / f"{target}.coma") for target in TARGETS),
    ]


def run_logged(cmd, log, env=None):
    print(shlex.join(map(str, cmd)), flush=True)
    with log.open("w") as stream:
        process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   text=True, env=env)
        for line in process.stdout:
            print(line, end="", flush=True)
            stream.write(line)
        require(process.wait() == 0, f"Command failed; inspect {log}")


def check_support(check, run):
    require(check.digest(BASELINE) == BASELINE_SHA, "Supporting manifest changed")
    config = tomllib.loads((VERSION / "crate/proofs.toml").read_text())
    require(config["tool"] == {"name": "creusot", "version": "0.13.0", "target": "annotated"},
            "Unexpected submission tool/scope")
    require(config.get("git", {}).get("remote") == "origin", "Review the submission remote")
    version = subprocess.check_output(["cargo", "creusot", "version"], text=True)
    require(version.splitlines()[0] == "cargo-creusot 0.13.0", "Activate Creusot 0.13.0")
    subprocess.run(["cargo", "metadata", "--locked", "--no-deps", "--format-version", "1"],
                   check=True, stdout=subprocess.DEVNULL)
    run_logged([sys.executable, str(REPO / "scripts/audit-proof-evidence.py"), str(VERSION),
                "--manifest", str(BASELINE), "--reconstruct-root-goals"], run / "support-audit.log")


def snapshot(check):
    values = check.input_hashes()
    # The submission command and report are additional inputs, not retroactive
    # additions to the immutable full-suite manifest.
    for path in [Path(__file__).resolve(), VERSION / "crate/proofs.toml",
                 VERSION / "verification/recorder/pin.json",
                 VERSION / "verification/recorder/cargo-proofs-0.3.5-external-traits.patch",
                 Path(os.environ["XDG_DATA_HOME"]) / "creusot/creusot_why3.conf"]:
        values[str(path)] = check.digest(path)
    return values


def check_local(check, base):
    actual = {str(path.parent.relative_to(base)) for path in base.rglob("proof.json")}
    require(actual == set(TARGETS), f"Unexpected/missing fresh sessions: {actual}")
    sessions = {}
    for target, source in TARGETS.items():
        coma = base / f"{target}.coma"
        header = re.fullmatch(r'\(\* #"([^"]+)" (\d+) (\d+) (\d+) (\d+) \*\)',
                              coma.read_text().splitlines()[0])
        require(header is not None, f"Missing declaration source span: {target}")
        path, first, _, last, _ = header.groups()
        require(Path(path).is_absolute() and Path(path).resolve() == (VERSION / source).resolve(),
                f"Wrong declaration source: {target}")
        lines = (VERSION / source).read_text().splitlines()
        require(1 <= int(first) <= int(last) <= len(lines), f"Invalid declaration span: {target}")
        name = target.rsplit("/", 1)[-1]
        require(re.search(rf"\bfn {name}\b", "\n".join(lines[int(first)-1:int(last)])),
                f"Span does not contain the expected method: {target}")
        item = check.session(base, target)
        require(item["goals"] > 0 and not item["open_goals"], f"Open/empty proof: {target}")
        item["source_span"] = {"file": source, "first_line": int(first), "last_line": int(last)}
        sessions[target] = item
    return sessions


def check_sarif(path):
    """Read actual recorder output; never synthesize or amend SARIF."""
    require(path.stat().st_size <= 8 * 1024 * 1024, "SARIF exceeds the service limit")
    document = json.loads(path.read_text())
    require(document["version"] == "2.1.0" and len(document["runs"]) == 1, "Unexpected SARIF")
    run = document["runs"][0]
    proof = run["properties"]["proofs"]
    require(proof["schemaVersion"] == 2 and isinstance(proof["dependencies"], list),
            "A version 2 dependency snapshot is required")
    require((proof["crate"], proof["version"], proof["target"]) == ("httpdate", "1.0.3", "annotated"),
            "Wrong package/scope")
    require(run["tool"]["driver"] == {"name": "creusot", "version": "0.13.0"}, "Wrong verifier")
    require(run["invocations"][0]["executionSuccessful"] is True, "Recording failed")
    contracts = proof["contracts"]
    require(len(contracts) == 4, "Exactly four verified API contracts are required")
    actual = {api for contract in contracts for api in contract["api_paths"]}
    require(actual == APIS, f"Unexpected/missing API identities: {sorted(actual)}")
    harnesses = {contract["harness"] for contract in contracts}
    require(len(harnesses) == 4, "Duplicate contract harness")
    results = run["results"]
    require(results and all(item["kind"] == "pass" for item in results), "Open/empty results")
    require({item["properties"]["harness"] for item in results} == harnesses,
            "Contract/result mismatch")
    expected_paths = {"httpdate/1.0.3/crate/src/lib.rs", "httpdate/1.0.3/crate/src/date.rs"}
    require(all(c["file"] in expected_paths and 0 < c["first_line"] <= c["last_line"]
                for c in contracts), "Missing/wrong source locations")
    print(f"SARIF scope checked: four APIs, {len(results)} passing results: {path}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("local", "record", "check-sarif"))
    parser.add_argument("--sarif", type=Path)
    parser.add_argument("--recorder", type=Path, default=REPO / ".local-verification/submission-tools/httpdate/bin/cargo-proofs")
    args = parser.parse_args()
    if args.mode == "check-sarif":
        require(args.sarif is not None, "Supply --sarif PATH")
        check_sarif(args.sarif)
        return
    os.chdir(VERSION)
    (VERSION / "verif").mkdir(exist_ok=True)
    run = Path(tempfile.mkdtemp(prefix="submission-", dir=VERSION / "verif"))
    print(f"Local diagnostics: {run}", flush=True)
    check = checker()
    check_support(check, run)
    before = snapshot(check)
    (run / "inputs.json").write_text(json.dumps(before, indent=2) + "\n")
    cmd = command(Path("verif") / run.name / "coma")
    if args.mode == "local":
        # A new target directory ensures Cargo actually emits fresh Coma.
        env = dict(os.environ, CARGO_TARGET_DIR=str(VERSION / "target" / run.name))
        run_logged(cmd, run / "verify.log", env)
        sessions = check_local(check, run / "coma/verif/httpdate_rlib")
        require(before == snapshot(check), "Inputs changed during local verification")
        (run / "checked.json").write_text(json.dumps({
            "kind": "local submission preflight; not a cargo-proofs recording",
            "support_manifest_sha256": BASELINE_SHA, "command": cmd,
            "sessions": sessions, "total_goals": sum(s["goals"] for s in sessions.values()),
        }, indent=2) + "\n")
        print(f"Local API proofs and source spans checked: {run / 'checked.json'}")
    else:
        # Explicit binary path keeps the archival cargo-proofs 0.3.4 on PATH.
        recorder = args.recorder.resolve(strict=True)
        version = subprocess.check_output([str(recorder), "--version"], text=True).strip()
        require(version == "cargo proofs 0.3.5", "Use the reviewed cargo-proofs 0.3.5 recorder")
        pin = json.loads((VERSION / "verification/recorder/pin.json").read_text())
        installation = json.loads((recorder.parent.parent / "installation.json").read_text())
        require(installation["source_commit"] == pin["source_commit"]
                and installation["patch_sha256"] == pin["patch_sha256"]
                and installation["binary_sha256"] == check.digest(recorder),
                "Install the pinned recorder with setup-submission-recorder.py")
        require(not subprocess.check_output(["git", "status", "--porcelain"], text=True).strip(),
                "Commit the reviewed inputs and push them to origin before recording")
        log = run / "record.log"
        run_logged([str(recorder), "run", "-p", "httpdate", "--", *cmd], log)
        require(before == snapshot(check), "Inputs changed during recording")
        require(installation["binary_sha256"] == check.digest(recorder), "Recorder changed during run")
        saved = re.findall(r"^Saved run ([0-9a-f-]+): (.+)$", log.read_text(), re.MULTILINE)
        require(len(saved) == 1, "Cannot locate the actual recorded SARIF; inspect record.log")
        uuid.UUID(saved[0][0])
        check_sarif(Path(saved[0][1]) / "run.sarif.json")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
