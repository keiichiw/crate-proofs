#!/usr/bin/env python3
"""Check isolated candidate provenance without modifying the pinned source."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

candidate = Path(__file__).resolve().parent
version = candidate.parents[1]
upstream = version / "upstream"
# The parent check independently ties the clean Git checkout to the registry archive.
subprocess.run([sys.executable, str(version / "scripts" / "check-source.py")], check=True)
record = json.loads((candidate / "provenance.json").read_text())
assert subprocess.check_output(["git", "-C", str(upstream), "rev-parse", "HEAD"], text=True).strip() == record["upstream_git_commit"]
assert not subprocess.check_output(["git", "-C", str(upstream), "status", "--porcelain"], text=True).strip()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for name, expected in record["upstream_src_sha256"].items():
    assert sha(upstream / "src" / name) == expected, name
for name, expected in record["candidate_src_sha256"].items():
    assert sha(candidate / "src" / name) == expected, name
    if name != "ipnet_serde.rs":
        assert (candidate / "src" / name).read_bytes() == (upstream / "src" / name).read_bytes(), name
original = (upstream / "src" / "ipnet_serde.rs").read_text()
expected = original.replace(
    '#[cfg(feature = "ser_as_str")]',
    '#[cfg(any(feature = "heapless", feature = "ser_as_str"))]'
).replace(
    '#[cfg(not(feature = "ser_as_str"))]',
    '#[cfg(not(any(feature = "heapless", feature = "ser_as_str")))]'
)
assert original.count('#[cfg(feature = "ser_as_str")]') == 2
assert original.count('#[cfg(not(feature = "ser_as_str"))]') == 2
assert (candidate / "src" / "ipnet_serde.rs").read_text() == expected
base_manifest = (version / "Cargo.toml").read_text()
assert base_manifest.count('path = "upstream/src/lib.rs"') == 1
assert (candidate / "Cargo.toml").read_text() == base_manifest.replace('path = "upstream/src/lib.rs"', 'path = "src/lib.rs"')
assert (candidate / "Cargo.lock").read_bytes() == (version / "Cargo.lock").read_bytes()
for label, p in [
    ("base_manifest_sha256", version / "Cargo.toml"),
    ("base_lock_sha256", version / "Cargo.lock"),
    ("candidate_manifest_sha256", candidate / "Cargo.toml"),
    ("candidate_lock_sha256", candidate / "Cargo.lock"),
]:
    assert sha(p) == record[label], label
assert sha(candidate / "cfg.patch") == record["cfg_patch_sha256"]
print("candidate source provenance PASS: unchanged upstream; one four-guard cfg edit; lock identical")
