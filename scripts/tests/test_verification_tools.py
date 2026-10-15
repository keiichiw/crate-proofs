"""Failure-boundary tests for the reusable tools; fixtures are not proof evidence."""
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
CAPTURE = ROOT / "scripts/capture-crate-release.py"
AUDIT = ROOT / "scripts/audit-proof-evidence.py"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def hashes(directory):
    return {p.relative_to(directory).as_posix(): sha(p) for p in directory.rglob("*") if p.is_file()}


class ReleaseTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.archive = self.base / "input.crate"
        self.metadata = self.base / "metadata.json"
        self.output = self.base / "capture"
        self.make_archive()

    def make_archive(self, unsafe=None):
        with tarfile.open(self.archive, "w:gz") as archive:
            for name, content in {"example-1.2.3/Cargo.toml": b'[package]\nname="example"\nversion="1.2.3"\n',
                                  "example-1.2.3/src/lib.rs": b"pub fn value() -> u8 { 1 }\n"}.items():
                entry = tarfile.TarInfo(name)
                entry.size = len(content)
                entry.mode = 0o644
                archive.addfile(entry, io.BytesIO(content))
            if unsafe:
                entry = tarfile.TarInfo(unsafe)
                if unsafe.endswith("link"):
                    entry.type = tarfile.SYMTYPE
                    entry.linkname = "../../outside"
                    archive.addfile(entry)
                else:
                    entry.size = 1
                    archive.addfile(entry, io.BytesIO(b"x"))
        self.metadata.write_text(json.dumps({"version": {"crate": "example", "num": "1.2.3",
                                                         "checksum": sha(self.archive)}}))

    def capture(self, success=True):
        result = subprocess.run([sys.executable, str(CAPTURE), "example", "1.2.3", "--output", str(self.output),
                                 "--metadata-file", str(self.metadata), "--archive-file", str(self.archive)],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)

    def check(self, success=True):
        before = hashes(self.output)
        result = subprocess.run([sys.executable, str(CAPTURE), "--check", str(self.output)], capture_output=True, text=True)
        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)
        self.assertEqual(hashes(self.output), before, "Read-only capture check modified files")

    def test_roundtrip_without_vcs_metadata(self):
        self.capture()
        self.check()
        self.assertIsNone(json.loads((self.output / "manifest.json").read_text())["release_vcs_info"])

    def test_changed_extracted_source(self):
        self.capture()
        (self.output / "source/src/lib.rs").write_text("changed")
        self.check(False)

    def test_extra_source(self):
        self.capture()
        (self.output / "source/src/extra.rs").write_text("unexpected")
        self.check(False)

    def test_added_source_symlink(self):
        self.capture()
        (self.output / "source/src/alias.rs").symlink_to("lib.rs")
        self.check(False)

    def test_bad_archive_checksum(self):
        self.archive.write_bytes(self.archive.read_bytes() + b"modified")
        self.capture(False)
        self.assertFalse(self.output.exists())

    def test_wrong_registry_identity(self):
        data = json.loads(self.metadata.read_text())
        data["version"]["crate"] = "another-crate"
        self.metadata.write_text(json.dumps(data))
        self.capture(False)

    def test_archive_traversal(self):
        self.make_archive("example-1.2.3/../../outside")
        self.capture(False)
        self.assertFalse((self.base / "outside").exists())

    def test_archive_symlink(self):
        self.make_archive("example-1.2.3/link")
        self.capture(False)

    def test_refuses_existing_output(self):
        self.capture()
        before = hashes(self.output)
        self.capture(False)
        self.assertEqual(hashes(self.output), before)


class EvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.version = Path(self.temp.name)
        source = self.version / "crate/src/lib.rs"
        source.parent.mkdir(parents=True)
        source.write_text("pub fn primary() {}\n")
        self.evidence = self.version / "verification/evidence/latest"
        self.target = self.evidence / "core/primary"
        self.target.mkdir(parents=True)
        self.proof = self.target / "proof.json"
        self.coma = self.target / "target.coma"
        self.coma.write_text("goal vc_auxiliary: true\ngoal vc_primary: true\n")
        self.proof_data = {"proofs": {"Coma": {"vc_auxiliary": {"prover": "fixture-only"},
                                             "vc_primary": {"prover": "fixture-only"}}}}
        self.proof.write_text(json.dumps(self.proof_data))
        self.item = {"goals": 2, "open_goals": [],
                     "goal_inventory": ["Coma.vc_auxiliary", "Coma.vc_primary"]}
        self.record = {"cache": False, "inputs_sha256": {"crate/src/lib.rs": sha(source)},
                       "targets": {"core/primary": self.item}, "expected_open": {},
                       "excluded_generated": {}, "generated_target_count": 1,
                       "total_session_goals": 2}
        self.save()

    def save(self):
        self.proof.write_text(json.dumps(self.proof_data))
        self.item["proof_json_sha256"] = sha(self.proof)
        self.item["coma_sha256"] = sha(self.coma)
        (self.evidence / "manifest.json").write_text(json.dumps(self.record))

    def audit(self, success=True, extra=()):
        before = hashes(self.version)
        result = subprocess.run([sys.executable, str(AUDIT), str(self.version), *map(str, extra)],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)
        self.assertEqual(hashes(self.version), before, "Audit modified version files")

    def test_consistent_saved_record(self):
        self.audit()

    def test_changed_input(self):
        (self.version / "crate/src/lib.rs").write_text("changed")
        self.audit(False)

    def test_new_unrecorded_rust_source(self):
        (self.version / "crate/src/extra.rs").write_text("new source")
        self.audit(False)

    def test_new_unrecorded_rust_symlink_alias(self):
        (self.version / "crate/src/alias.rs").symlink_to("lib.rs")
        self.audit(False)

    def test_changed_coma(self):
        self.coma.write_text(self.coma.read_text() + "\n")
        self.audit(False)

    def test_zero_goals(self):
        self.proof_data["proofs"] = {}
        self.save()
        self.audit(False)

    def test_missing_target_vc(self):
        del self.proof_data["proofs"]["Coma"]["vc_primary"]
        self.item.update(goals=1, goal_inventory=["Coma.vc_auxiliary"])
        self.record["total_session_goals"] = 1
        self.save()
        self.audit(False)

    def test_unproved_selected_goal(self):
        self.proof_data["proofs"]["Coma"]["vc_primary"] = {}
        self.save()
        self.audit(False)

    def test_vacuous_tactic(self):
        self.proof_data["proofs"]["Coma"]["vc_primary"] = {"tactic": "split", "children": []}
        self.save()
        self.audit(False)

    def test_extra_session(self):
        directory = self.evidence / "core/unexpected"
        shutil.copytree(self.target, directory)
        self.audit(False)

    def test_missing_generated_exclusion(self):
        self.record["excluded_generated"] = {"core/private": "Not selected"}
        self.record["generated_target_count"] = 2
        self.save()
        generated = self.version / "fresh-coma/core"
        generated.mkdir(parents=True)
        shutil.copyfile(self.coma, generated / "primary.coma")
        self.audit(False, ("--generated-dir", generated.parent))

    def add_open(self):
        directory = self.evidence / "core/convert__refines"
        directory.mkdir(parents=True)
        proof = directory / "proof.json"
        coma = directory / "target.coma"
        proof.write_text(json.dumps({"proofs": {"Coma": {"refines": {}}}}))
        coma.write_text("goal refines: true\n")
        self.record["expected_open"] = {"core/convert__refines": {
            "goals": 1, "open_goals": ["Coma.refines"], "goal_inventory": ["Coma.refines"],
            "proof_json_sha256": sha(proof), "coma_sha256": sha(coma), "reason": "Fixture open refinement"}}
        self.record["generated_target_count"] = 2
        (self.evidence / "open-prove.exit").write_text("1\n")
        self.save()

    def test_expected_open_separate_from_positive(self):
        self.add_open()
        self.audit()

    def test_abnormal_open_exit(self):
        self.add_open()
        (self.evidence / "open-prove.exit").write_text("124\n")
        self.audit(False)

    def test_resolved_expected_open_needs_reclassification(self):
        self.add_open()
        proof = self.evidence / "core/convert__refines/proof.json"
        proof.write_text(json.dumps({"proofs": {"Coma": {"refines": {"prover": "fixture-only"}}}}))
        item = self.record["expected_open"]["core/convert__refines"]
        item.update(open_goals=[], proof_json_sha256=sha(proof))
        self.save()
        self.audit(False)

    def test_duplicate_json_goal_key(self):
        self.proof.write_text('{"proofs":{"Coma":{"vc_primary":{"prover":"fixture-only"},'
                              '"vc_primary":{"prover":"fixture-only"},"vc_auxiliary":{"prover":"fixture-only"}}}}')
        self.item["proof_json_sha256"] = sha(self.proof)
        (self.evidence / "manifest.json").write_text(json.dumps(self.record))
        self.audit(False)

    @unittest.skipUnless(shutil.which("why3"), "Activate the pinned Why3 environment for independent reconstruction")
    def test_independent_root_reconstruction_rejects_self_consistent_omission(self):
        self.audit(True, ("--reconstruct-root-goals",))
        del self.proof_data["proofs"]["Coma"]["vc_auxiliary"]
        self.item.update(goals=1, goal_inventory=["Coma.vc_primary"])
        self.record["total_session_goals"] = 1
        self.save()
        # Internal consistency alone cannot discover this omitted auxiliary VC.
        self.audit(True)
        self.audit(False, ("--reconstruct-root-goals",))


if __name__ == "__main__":
    unittest.main()
