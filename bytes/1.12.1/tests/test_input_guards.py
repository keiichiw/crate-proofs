"""Integration guards for a prepared workspace; each mutation is restored exactly."""
import json,subprocess,sys,unittest
from pathlib import Path
r=Path(__file__).resolve().parents[1];p=r/'aeneas/profiles/default'
class GuardTests(unittest.TestCase):
 def check_rejected(self,path,change,diagnostic):
  original=path.read_bytes()
  try:
   path.write_text(change(original.decode()))
   result=subprocess.run([sys.executable,str(r/'scripts/check-managed-inputs.py')],capture_output=True,text=True)
   self.assertNotEqual(result.returncode,0)
   self.assertIn(diagnostic,result.stderr)
  finally:path.write_bytes(original)
 def test_empty_prelude_correspondence_rejected(self):
  def change(raw):
   value=json.loads(raw);value['prelude_copies']={};return json.dumps(value)
  self.check_rejected(p/'stage3-tool-repair.json',change,'Incomplete stage3')
 def test_outer_manifest_semantics_rejected(self):
  self.check_rejected(r/'Cargo.toml',lambda text:text.replace('edition = "2021"','edition = "2024"'),'Outer release manifest')
 def test_missing_numeric_repair_delta_rejected(self):
  def change(raw):
   value=json.loads(raw);value['additional_changed_files_from_core']=[];return json.dumps(value)
  self.check_rejected(p/'numeric-tool-repair.json',change,'Numeric repair delta')
 def test_captured_standard_source_symlink_rejected(self):
  path=p/'stdlib-source/library/core/src/ops/range.rs';original=path.read_bytes();backup=path.with_name('range.test-backup');backup.write_bytes(original)
  try:
   path.unlink();path.symlink_to(backup.name)
   result=subprocess.run([sys.executable,str(r/'scripts/check-managed-inputs.py')],capture_output=True,text=True)
   self.assertNotEqual(result.returncode,0);self.assertIn('Captured standard source must be regular',result.stderr)
  finally:path.unlink();path.write_bytes(original);backup.unlink()
if __name__=='__main__':unittest.main()
