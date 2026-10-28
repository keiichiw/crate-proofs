import importlib.util
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('evidence', Path(__file__).parents[1] / 'aeneas_evidence.py')
evidence = importlib.util.module_from_spec(spec)
spec.loader.exec_module(evidence)


class EvidenceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='evidence path with spaces ')
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.source = self.root / 'run'
        self.source.mkdir()
        self.store = self.root / '.work/archives'
        (self.source / 'build.log').write_bytes(b'PRIVATE RAW LOG\r\n')
        (self.source / 'command.sh').write_bytes(b'#!/bin/sh\nexit 0\n')
        (self.source / 'command.sh').chmod(0o755)

    def test_deterministic_archive_and_exact_restore(self):
        a = evidence.archive(self.source, self.store)
        b = evidence.archive(self.source, self.store)
        self.assertEqual(a, b)
        self.assertEqual(a['availability'], 'local-only')
        self.assertIsNone(a['public_url'])
        destination = self.root / 'restored space'
        evidence.restore(a, self.store, destination)
        self.assertEqual(evidence.inventory(self.source), evidence.inventory(destination))
        with self.assertRaises(ValueError):
            evidence.restore(a, self.store, destination)

    def test_corrupt_archive_rejected(self):
        record = evidence.archive(self.source, self.store)
        with (self.store / record['archive']).open('ab') as handle:
            handle.write(b'corrupt')
        with self.assertRaises(ValueError):
            evidence.verify(record, self.store)

    def test_symlink_and_recursive_store_rejected(self):
        (self.source / 'link').symlink_to(self.source / 'build.log')
        with self.assertRaises(ValueError):
            evidence.archive(self.source, self.store)
        (self.source / 'link').unlink()
        with self.assertRaises(ValueError):
            evidence.archive(self.source, self.source / 'archive')

    def rewrite_archive(self, record, alter):
        path = self.store / record['archive']
        with tarfile.open(path) as tar:
            items = [(m, tar.extractfile(m).read()) for m in tar.getmembers()]
        items = alter(items)
        changed = self.root / 'changed.tar.gz'
        with tarfile.open(changed, 'w:gz') as tar:
            for item, data in items:
                tar.addfile(item, io.BytesIO(data))
        record = {**record, 'sha256': evidence.file_sha(changed)}
        record['archive'] = record['sha256'] + '.tar.gz'
        changed.rename(self.store / record['archive'])
        return record

    def test_member_inventory_checks_even_with_valid_outer_hash(self):
        record = evidence.archive(self.source, self.store)
        for alter in [lambda xs: xs[:-1], lambda xs: xs + [xs[-1]]]:
            changed = self.rewrite_archive(record, alter)
            with self.assertRaises(ValueError):
                evidence.verify(changed, self.store)
        def traversal(items):
            items[-1][0].name = 'payload/../../escape'
            return items
        changed = self.rewrite_archive(record, traversal)
        with self.assertRaises(ValueError):
            evidence.verify(changed, self.store)
        self.assertFalse((self.root / 'escape').exists())

    def make_run(self):
        (self.source / 'audit').mkdir()
        audit = {'status': 'passed', 'checked': [{'name': 'test_theorem'}],
                 'allowed_axioms': ['propext'], 'files_sha256': {}}
        evidence.write_json(self.source / 'audit/result.json', audit)
        for name in ('inputs-before.json', 'inputs-after.json'):
            evidence.write_json(self.source / name, {'input': 'fixed'})
        result = {'status': 'passed', 'profile': 'default', 'host': 'test-host', 'target': 'test-target',
                  'files_sha256': {n: e['sha256'] for n, e in evidence.inventory(self.source).items()}}
        evidence.write_json(self.source / 'result.json', result)
        return evidence.archive(self.source, self.store)

    def test_summary_preserves_scope_without_embedding_logs(self):
        record = self.make_run()
        summary = evidence.summarize(self.source, record)
        self.assertEqual(summary['audit']['checked'], [{'name': 'test_theorem'}])
        self.assertNotIn('PRIVATE RAW LOG', json.dumps(summary))
        self.assertNotIn('#!/bin/sh', json.dumps(summary))
        self.assertEqual(summary['reported_status'], 'passed')

    def test_successful_custom_script_cannot_hide_failed_audit(self):
        record = self.make_run()
        path = self.source / 'audit/result.json'
        path.write_text(json.dumps({'status': 'failed'}))
        with self.assertRaises(ValueError):
            evidence.summarize(self.source, record)

    def test_changed_inputs_or_missing_log_rejected(self):
        record = self.make_run()
        (self.source / 'inputs-after.json').write_text('{}')
        with self.assertRaises(ValueError):
            evidence.summarize(self.source, record)
        (self.source / 'inputs-after.json').write_bytes((self.source / 'inputs-before.json').read_bytes())
        (self.source / 'build.log').unlink()
        with self.assertRaises(ValueError):
            evidence.summarize(self.source, record)

    def test_publication_lint_needs_no_archive_and_rejects_unlisted_logs(self):
        record = self.make_run()
        published = self.root / 'evidence'
        published.mkdir()
        evidence.write_json(published / 'archive.json', record)
        evidence.write_json(published / 'summary.json', evidence.summarize(self.source, record))
        evidence.check_publication(published)
        (published / 'unexpected.log').write_text('build output')
        with self.assertRaises(ValueError):
            evidence.check_publication(published)


if __name__ == '__main__':
    unittest.main()
