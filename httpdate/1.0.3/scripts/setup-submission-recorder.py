#!/usr/bin/env python3
"""Install the pinned, locally patched recorder without replacing archived tools."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

version = Path(__file__).resolve().parents[1]
repo = version.parents[1]
pins = version / "verification/recorder/pin.json"
pin = json.loads(pins.read_text())
patch = pins.parent / pin["patch"]
root = repo / ".local-verification/submission-tools/httpdate"
root.mkdir(parents=True, exist_ok=True)
build = Path(tempfile.mkdtemp(prefix="build-", dir=root))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise SystemExit(message)


require(sha(patch) == pin["patch_sha256"], "Recorder patch hash mismatch")
archive = build / "source.tar.gz"
subprocess.run(["curl", "--fail", "--location", "--show-error", "--silent", "--max-time", "120",
                f"https://codeload.github.com/proofs-rs/proofs-rs/tar.gz/{pin['source_commit']}",
                "--output", str(archive)], check=True)
require(sha(archive) == pin["archive_sha256"], "Recorder source archive hash mismatch")
source = build / "source"
source.mkdir()
subprocess.run(["tar", "-xzf", str(archive), "--strip-components=1", "-C", str(source)], check=True)
subprocess.run(["patch", "--batch", "-p1", "-i", str(patch)], cwd=source, check=True)
manifest = source / "cli/Cargo.toml"
target = root / "target"
with (build / "tests.log").open("w") as log:
    tests = subprocess.run(["cargo", "test", "--locked", "--release", "--manifest-path", str(manifest),
                            "--target-dir", str(target)], stdout=log, stderr=subprocess.STDOUT)
require(tests.returncode == 0, f"Recorder tests failed: {build / 'tests.log'}")
subprocess.run(["cargo", "install", "--locked", "--path", str(source / "cli"),
                "--root", str(root), "--target-dir", str(target), "--force"], check=True)
binary = root / "bin/cargo-proofs"
(root / "installation.json").write_text(json.dumps({
    "source_commit": pin["source_commit"], "patch_sha256": sha(patch),
    "binary_sha256": sha(binary), "source": str(source),
    "tests_log": str(build / "tests.log"),
}, indent=2) + "\n")
print(f"Installed isolated submission recorder: {binary}")
print(f"Tests: {build / 'tests.log'}")
