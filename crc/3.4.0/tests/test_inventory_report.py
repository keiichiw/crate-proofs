"""Inventory checks preserve prose while rejecting changes to formal bindings."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

PROFILE = Path(__file__).resolve().parents[1] / 'aeneas/profiles/stage2'


class InventoryReport(unittest.TestCase):
    def test_editorial_changes_and_binding_mutations(self):
        mutations = {
            'none': None,
            'prose': ('selected checksum and digest contracts', 'reviewed CRC contracts'),
            'literal_table_in_title': ('selected checksum and digest contracts', 'reviewed [tool] contracts'),
            'literal_table_in_prose': ('For the built-in', '[tool]\nFor the built-in'),
            'api': ('Crc<u8, Table<0>>::digest"', 'Crc<u8, Table<1>>::digest"'),
            'theorem': ('CrcPublicWordInstances.digest8_lane0_spec', 'Unknown.theorem'),
            'module': ('Stage2Proofs.WordProtocolInstances', 'Unknown.Module'),
            'precondition': ('1 <= current algorithm.width <= 8;', '0 <= current algorithm.width <= 8;'),
            'tool_version': ('version = "be86ab0f1989d04944292b345b24c435be3ad10a"', 'version = "other"'),
        }
        for name, mutation in mutations.items():
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory) / 'crate/aeneas/profiles/stage2'
                shutil.copytree(PROFILE, root, ignore=shutil.ignore_patterns('.lake', 'evidence'))
                report = root / 'proofs.toml'
                text = report.read_text()
                if mutation:
                    self.assertIn(mutation[0], text)
                    text = text.replace(*mutation, 1)
                    report.write_text(text)
                command = [sys.executable, root / 'adapter/inventory.py']
                result = subprocess.run(command + ['--check'], capture_output=True, text=True)
                accepted = name in ('none', 'prose', 'literal_table_in_title', 'literal_table_in_prose')
                self.assertEqual(result.returncode == 0, accepted, result.stderr)
                self.assertEqual(report.read_text(), text)
                if accepted:
                    result = subprocess.run(command, capture_output=True, text=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(report.read_text(), text)


if __name__ == '__main__':
    unittest.main()
