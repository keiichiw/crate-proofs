"""Current generic specialization guards; no previous inventory is read."""
from pathlib import Path
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
PROFILE = Path(__file__).resolve().parents[1] / 'aeneas/profiles/stage2'

class ProtocolWrappers(unittest.TestCase):
    def test_current_wrappers_and_negative_mutations(self):
        for mutation in ('none', 'lane', 'result', 'binder', 'inventory'):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                (root / 'adapter').mkdir();(root / 'proofs/Stage2Proofs').mkdir(parents=True)
                for name in ('WordProtocols.lean','WordProtocolInstances.lean'):
                    shutil.copyfile(PROFILE / 'proofs/Stage2Proofs' / name, root / 'proofs/Stage2Proofs' / name)
                shutil.copyfile(PROFILE / 'adapter/check-word-instances.py', root / 'adapter/check.py')
                shutil.copyfile(PROFILE / 'theorems.json', root / 'theorems.json')
                p = root / 'proofs/Stage2Proofs/WordProtocolInstances.lean'
                s = p.read_text()
                if mutation == 'lane': s = s.replace('0#usize','1#usize',1)
                elif mutation == 'result': s = s.replace('∃','∀',1)
                elif mutation == 'binder': s = s.replace('hw :','unexpected :',1)
                elif mutation == 'inventory':
                    d = json.loads((root / 'theorems.json').read_text())
                    d['checked'] = [x for x in d['checked'] if not x['name'].startswith('CrcPublicWordInstances.')]
                    (root / 'theorems.json').write_text(json.dumps(d))
                p.write_text(s)
                process = subprocess.run([sys.executable, root / 'adapter/check.py'], capture_output=True,text=True)
                self.assertEqual(process.returncode == 0, mutation == 'none', process.stderr)

if __name__ == '__main__': unittest.main()
