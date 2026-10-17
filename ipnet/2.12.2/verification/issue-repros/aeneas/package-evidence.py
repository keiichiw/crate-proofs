#!/usr/bin/env python3
"""Copy a fresh successful diagnostic run into commit-ready evidence."""
import hashlib
import json
from pathlib import Path
import shutil
import sys

root = Path(__file__).resolve().parent
version = root.parents[2]
run = Path(sys.argv[1]).resolve()
assert run.parent == (root / "runs").resolve()
dest = root / "evidence/latest"
stage = root / "evidence/.stage"
if stage.exists():
    shutil.rmtree(stage)
stage.mkdir(parents=True)
names = []
for case in ("mutable_dyn_write", "next_ascii", "extend_bytes"):
    for leaf in ("charon.log", "aeneas.log", "aeneas.exit"):
        names.append((f"{case}/{leaf}", f"{case}/{leaf}"))
    for leaf in ("Repro.lean", "lean.log"):
        if (run / case / leaf).is_file():
            saved = "Repro.lean.txt" if leaf == "Repro.lean" else leaf
            names.append((f"{case}/{leaf}", f"{case}/{saved}"))
for source, saved in names:
    target = stage / saved
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(run / source, target)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
evidence = {
    "status": "all three expected tool failures reproduced",
    "run": run.name,
    "toolchain_json_sha256": sha(version / "verification/toolchain.json"),
    "source_sha256": sha(root / "src/lib.rs"),
    "manifest_sha256": sha(root / "Cargo.toml"),
    "lock_sha256": sha(root / "Cargo.lock"),
    "reproduce_script_sha256": sha(root / "reproduce.sh"),
    "files_sha256": {saved: sha(stage / saved) for _, saved in names},
}
if dest.exists():
    shutil.rmtree(dest)
stage.rename(dest)
(root / "evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")
print(dest)
