#!/usr/bin/env python3
"""Freshly reproduce four narrow, rejected aggregate extraction stages.

The diagnostics are packaged, not admitted into the maintained Lean model.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
VERSION = HERE.parents[2]
REPO = VERSION.parents[1]
RUN = Path(tempfile.mkdtemp(prefix="aggregate-refresh-", dir=VERSION / "verification/runs"))
cases = [
    ("01", "01-config.json", "01-extend-generated.txt"),
    ("02", "02-config.json", "02-spec-extend-generated.txt"),
    ("03", "03-config.json", "03-extend-desugared-generated.txt"),
    ("04", "04-ipv6-config.json", "04-ipv6-generated.txt"),
]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outcomes = []
staging = HERE / ".stage"
if staging.exists():
    shutil.rmtree(staging)
staging.mkdir()
for label, config, generated in cases:
    output = RUN / label
    env = os.environ.copy()
    env["CARGO_TARGET_DIR"] = str(RUN / "target")
    cmd = ["bash", "-c", f"source scripts/env.sh && python3 {REPO / 'scripts/aeneas-extract.py'} . "
           f"--config verification/blockers/aggregate-extend/{config} --output {output}"]
    p = subprocess.run(cmd, cwd=VERSION, env=env, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT)
    (staging / f"{label}-extract.log").write_bytes(p.stdout)
    assert p.returncode != 0, f"{config} unexpectedly accepted incomplete model"
    for source, dest in [("charon.log", f"{label}-charon.log"),
                         ("aeneas.log", f"{label}-aeneas.log"),
                         ("Ipnet.lean", generated)]:
        path = output / source
        assert path.is_file(), f"Missing {path}"
        shutil.copy2(path, staging / dest)
    text = (staging / generated).read_text()
    assert "extend" in text, f"Expected Vec dependency not emitted: {config}"
    outcomes.append({"case": label, "config": config,
                     "extract_exit": p.returncode, "generated": generated})
    print(label, p.returncode, flush=True)

# Replace only after all four expected rejections were observed.
for label, _config, generated in cases:
    for name in (f"{label}-extract.log", f"{label}-charon.log",
                 f"{label}-aeneas.log", generated):
        shutil.copy2(staging / name, HERE / name)
record = {
    "classification": "four expected incomplete-model rejections; no aggregate proof",
    "run": RUN.name,
    "active_aeneas_patch_sha256": sha(VERSION / "verification/patches/aeneas-runtime-ipv6-constructor.patch"),
    "active_aeneas_binary_sha256": sha(VERSION / ".tools/aeneas/bin/aeneas"),
    "outcomes": outcomes,
    "files_sha256": {p.name: sha(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name not in
                     {"evidence.json", "README.md"}},
}
(HERE / "evidence.json").write_text(json.dumps(record, indent=2) + "\n")
shutil.rmtree(staging)
print(HERE)
