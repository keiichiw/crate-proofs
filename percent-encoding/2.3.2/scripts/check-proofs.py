#!/usr/bin/env python3
"""Snapshot inputs and assemble an auditable direct SMT evidence bundle."""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

VERSION = Path(__file__).resolve().parent.parent
REPO = VERSION.parent.parent
FORM = REPO / "form_urlencoded/1.2.2"
FORM_EVIDENCE = FORM / "verification/evidence/direct-s8YxnYN7/manifest.json"
FORM_EVIDENCE_SHA256 = "d21f6c897107588209849a03f887bf2beff597be648160272c756c5d5ad0c9e8"


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def relative(path):
    path = Path(path).resolve()
    return str(path.relative_to(VERSION)) if path.is_relative_to(VERSION) else str(path)


def input_paths():
    files = set()
    # The release snapshot, workspace manifests, all checked source and documentation,
    # and every script that can affect translation or evidence production.
    for name in ("Cargo.toml", "Cargo.lock", "why3find.json", "AGENTS.md",
                 "crate/Cargo.lock", "crate/why3find.json", "crate/.cargo/config.toml",
                 "crate/Cargo.toml", "crate/Cargo.toml.orig", "crate/.cargo_vcs_info.json",
                 "capture/manifest.json", "capture/registry-metadata.json", "capture/release.crate",
                 "capture/source/Cargo.toml", "capture/source/Cargo.toml.orig",
                 "capture/source/Cargo.lock", "capture/source/.cargo_vcs_info.json"):
        p = VERSION / name
        if p.is_file(): files.add(p)
    for root in (VERSION / "crate/src", VERSION / "verification", VERSION / "scripts",
                 VERSION / "capture/source"):
        if root.is_dir():
            files.update(p for p in root.rglob("*") if p.is_file()
                         and p != VERSION / "verification/results.md"
                         and not any(part in {"evidence", "__pycache__", "verif"}
                                     or part == "target" or part.startswith("target-")
                                     for part in p.relative_to(VERSION).parts[:-1]))
    # Dependency identity and proof chain: hash the actual locked path dependency
    # (including its manifest and lockfile) and the previously audited proof manifest.
    require(FORM_EVIDENCE.is_file(), f"pinned form evidence manifest missing: {FORM_EVIDENCE}")
    require(sha(FORM_EVIDENCE) == FORM_EVIDENCE_SHA256,
            "pinned form evidence manifest no longer matches the reviewed SHA-256")
    for name in ("Cargo.toml", "Cargo.toml.orig", "Cargo.lock", ".cargo_vcs_info.json"):
        p = FORM / "crate" / name
        if p.is_file(): files.add(p)
    src = FORM / "crate/src"
    if src.is_dir(): files.update(p for p in src.rglob("*.rs") if p.is_file())
    files.add(FORM_EVIDENCE)
    # Creusot's Rust extern specifications are registry packages separate from
    # the Why3 model cache. Pin the exact packages Cargo resolves for this crate.
    metadata = subprocess.run(
        [shutil.which("cargo") or "cargo", "metadata", "--offline", "--locked",
         "--format-version", "1", "--manifest-path", str(VERSION / "crate/Cargo.toml")],
        cwd=VERSION / "crate", check=True, capture_output=True, text=True)
    packages = json.loads(metadata.stdout).get("packages", [])
    for name in ("creusot-std", "creusot-std-proc"):
        matches = [p for p in packages if p.get("name") == name and p.get("version") == "0.13.0"
                   and isinstance(p.get("source"), str)
                   and p["source"].startswith("registry+")]
        require(len(matches) == 1, f"Cargo metadata must resolve exactly one registry {name} 0.13.0")
        package_root = Path(matches[0]["manifest_path"]).resolve().parent
        require((package_root / "Cargo.toml").is_file() and (package_root / "src").is_dir(),
                f"resolved {name} package source tree is incomplete")
        files.update(p for p in package_root.rglob("*") if p.is_file())
    for name in ("rust-toolchain.toml", "scripts/activate.sh", "scripts/activate-local.sh", ".agents/skills/creusot-verification/SKILL.md",
                 "verification/playbook.md", "verification/tools.md"):
        p = REPO / name
        if p.is_file(): files.add(p)
    xdg = Path(os.environ.get("XDG_DATA_HOME", "/workspace/.local/share"))
    config = xdg / "creusot/creusot_why3.conf"
    require(config.is_file(), f"Why3 config missing: {config}")
    files.add(config)
    package = xdg / "creusot/share/why3find/packages/creusot"
    require(package.is_dir() and any(package.rglob("*.coma")), f"Creusot model package missing: {package}")
    files.update(p for p in package.rglob("*") if p.is_file())
    drivers = xdg / "creusot/_opam/share/why3/drivers"
    if drivers.is_dir(): files.update(p for p in drivers.rglob("*") if p.is_file())
    return sorted(files)


def tool_hashes():
    result = {}
    for name in ("cargo", "cargo-creusot", "rustup", "why3", "z3", "cvc5"):
        found = shutil.which(name)
        require(found is not None, f"required tool missing from activated PATH: {name}")
        path = Path(found).resolve()
        result[name] = {"path": str(path), "sha256": sha(path)}
        if name == "cvc5":
            version = subprocess.run([str(path), "--version"], check=True,
                capture_output=True, text=True).stdout.splitlines()
            require(version, "cvc5 --version returned no version identity")
            result[name]["version_line"] = version[0]
    wrapper = Path(os.environ.get("XDG_DATA_HOME", "/workspace/.local/share")) / \
        "creusot/toolchains/nightly-2026-06-22/bin/creusot-rustc"
    require(wrapper.is_file(), f"Creusot rustc wrapper missing: {wrapper}")
    result["creusot-rustc"] = {"path": str(wrapper), "sha256": sha(wrapper)}
    rustup = shutil.which("rustup")
    for label, channel in (("default", None), ("nightly-2026-06-22", "nightly-2026-06-22")):
        command = [rustup, "which", "rustc"] if channel is None else [
            rustup, "which", "--toolchain", channel, "rustc"]
        found = subprocess.run(command, check=True, capture_output=True, text=True).stdout.strip()
        path = Path(found).resolve()
        result[f"rustc-{label}"] = {"path": str(path), "sha256": sha(path)}
    return result


def snapshot(path):
    record = {"created_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
              "inputs_sha256": {relative(p): sha(p) for p in input_paths()},
              "tools_sha256": tool_hashes()}
    Path(path).write_text(json.dumps(record, indent=2) + "\n")
    print(f"Snapshotted {len(record['inputs_sha256'])} files and {len(record['tools_sha256'])} tools.")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--snapshot", type=Path, required=True)
    args = ap.parse_args()
    snapshot(args.snapshot)


if __name__ == "__main__":
    try: main()
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
