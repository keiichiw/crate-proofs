import hashlib
import io
import json
from pathlib import Path
import sys
import tarfile
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from aeneas_management import source


class SourceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='aeneas test ')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.cache = self.root / 'cache'
        self.cache.mkdir()

    def archive(self, members):
        archive = self.root / 'input.crate'
        with tarfile.open(archive, 'w:gz') as tar:
            for name, text, kind in members:
                info = tarfile.TarInfo(name)
                info.type = kind
                info.size = len(text) if kind == tarfile.REGTYPE else 0
                info.linkname = '../../escaped' if kind == tarfile.SYMTYPE else ''
                tar.addfile(info, io.BytesIO(text) if info.size else None)
        return archive

    def fixture(self):
        archive = self.archive([('demo-1.0.0/src/lib.rs', b'pub fn f() {}\n', tarfile.REGTYPE),
                                ('demo-1.0.0/Cargo.lock', b'lock', tarfile.REGTYPE)])
        expanded = self.root / 'expanded'
        expanded.mkdir()
        source.extract_archive(archive, expanded, 'demo-1.0.0')
        lock = {'schema_version': 1, 'kind': 'registry', 'name': 'demo', 'version': '1.0.0',
                'url': 'https://static.crates.io/crates/demo/demo-1.0.0.crate',
                'sha256': source.digest(archive), 'files': source.inventory(expanded)}
        source.write_json(self.root / 'source.lock.json', lock)
        (self.cache / (lock['sha256'] + '.crate')).write_bytes(archive.read_bytes())
        return lock

    def test_offline_restore_and_repeat(self):
        lock = self.fixture()
        first = source.restore(self.root, offline=True, cache=self.cache)
        source.check(first, lock)
        self.assertEqual(first, source.restore(self.root, offline=True, cache=self.cache))
        self.assertTrue((first / 'Cargo.lock').is_file())

    def test_tracked_upstream_is_checked_without_restoration(self):
        lock = self.fixture()
        (self.root / 'expanded').rename(self.root / 'upstream')
        restored = source.restore(self.root, offline=True)
        self.assertEqual(restored, source.directory(self.root))
        self.assertFalse((self.root / '.work').exists())
        (restored / 'src/lib.rs').write_text('changed')
        with self.assertRaises(ValueError):
            source.restore(self.root, offline=True)
        self.assertEqual((restored / 'src/lib.rs').read_text(), 'changed')

    def test_parallel_restore(self):
        self.fixture()
        with ThreadPoolExecutor(max_workers=4) as pool:
            paths = list(pool.map(lambda _: source.restore(self.root, offline=True, cache=self.cache), range(4)))
        self.assertEqual(len(set(paths)), 1)

    def test_missing_cache_fails_without_partial_source(self):
        self.fixture()
        with self.assertRaisesRegex(ValueError, 'cache miss'):
            source.restore(self.root, offline=True, cache=self.root / 'empty')
        self.assertFalse((self.root / '.work/source').exists())

    def test_corrupt_archive_rejected(self):
        lock = self.fixture()
        (self.cache / (lock['sha256'] + '.crate')).write_bytes(b'wrong')
        with self.assertRaisesRegex(ValueError, 'Corrupt'):
            source.restore(self.root, offline=True, cache=self.cache)

    def test_changed_missing_and_extra_source_rejected(self):
        lock = self.fixture()
        root = source.restore(self.root, offline=True, cache=self.cache)
        p = root / 'src/lib.rs'
        original = p.read_bytes()
        p.write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError, 'changed='):
            source.check(root, lock)
        p.unlink()
        with self.assertRaisesRegex(ValueError, 'missing='):
            source.check(root, lock)
        p.write_bytes(original)
        p.chmod(0o644)
        (root / 'extra.rs').write_text('extra')
        with self.assertRaisesRegex(ValueError, 'extra='):
            source.check(root, lock)

    def test_executable_mode_is_part_of_identity(self):
        lock = self.fixture()
        root = source.restore(self.root, offline=True, cache=self.cache)
        (root / 'src/lib.rs').chmod(0o755)
        with self.assertRaises(ValueError):
            source.check(root, lock)

    def test_links_traversal_and_duplicate_rejected(self):
        for entries in [
            [('demo-1.0.0/../../escape', b'x', tarfile.REGTYPE)],
            [('demo-1.0.0/link', b'', tarfile.SYMTYPE)],
            [('demo-1.0.0/x', b'x', tarfile.REGTYPE)] * 2,
            [('/demo-1.0.0/x', b'x', tarfile.REGTYPE)],
        ]:
            with self.subTest(entries=entries), tempfile.TemporaryDirectory(dir=self.root) as out:
                with self.assertRaises(ValueError):
                    source.extract_archive(self.archive(entries), Path(out), 'demo-1.0.0')

    def test_symlink_source_rejected(self):
        lock = self.fixture()
        root = source.restore(self.root, offline=True, cache=self.cache)
        (root / 'alias').symlink_to(root / 'src/lib.rs')
        with self.assertRaisesRegex(ValueError, 'Symlink'):
            source.check(root, lock)

    def test_lock_cannot_redirect_registry(self):
        lock = self.fixture()
        lock['url'] = 'https://example.invalid/archive'
        with self.assertRaises(ValueError):
            source.validate_lock(lock)


if __name__ == '__main__':
    unittest.main()
