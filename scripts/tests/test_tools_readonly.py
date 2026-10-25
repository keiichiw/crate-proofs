from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / 'scripts'))
from aeneas_management import tools

# Exact previous recipe reviewed in recipe-compatibility.json. Older context-free
# recipes and arbitrary predecessors are intentionally ineligible.
OLD_RECIPE_SHA256 = 'c932f58c9107e63993f15691454b860593ec6865d912f300cc957d8052bf72f0'



class ReadOnlySourceCheck(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.repo = Path(self.temp.name)
        self.git('init', '-q')
        self.git('config', 'user.name', 'Read Only Test')
        self.git('config', 'user.email', 'test@example.invalid')
        self.git('remote', 'add', 'origin', 'https://example.invalid/pinned.git')
        (self.repo / 'source').write_text('base\n')
        self.git('add', 'source')
        self.git('commit', '-qm', 'base')
        base = self.git('rev-parse', 'HEAD')
        (self.repo / 'source').write_text('patched\n')
        self.git('add', 'source')
        self.spec = {'url': 'https://example.invalid/pinned.git',
                     'revision': base, 'tree': self.git('write-tree')}

    def tearDown(self):
        self.temp.cleanup()

    def git(self, *args):
        return subprocess.check_output(['git', '-C', str(self.repo), *args], stderr=subprocess.PIPE).decode().strip()

    def test_parallel_check_with_held_index_lock_is_read_only(self):
        index = self.repo / '.git/index'
        before = (index.read_bytes(), index.stat().st_mtime_ns)
        lock = self.repo / '.git/index.lock'
        lock.write_bytes(b'held by a different legitimate Git operation\n')
        sentinel = (lock.read_bytes(), lock.stat().st_mtime_ns)
        with ThreadPoolExecutor(max_workers=8) as executor:
            list(executor.map(lambda _: tools.source_check(self.repo, self.spec), range(24)))
        self.assertEqual((index.read_bytes(), index.stat().st_mtime_ns), before)
        self.assertEqual((lock.read_bytes(), lock.stat().st_mtime_ns), sentinel)

    def test_fresh_patch_restore_materializes_previously_absent_tree(self):
        patch_bytes = subprocess.check_output(['git', '-C', str(self.repo),
                                              'diff', '--cached', '--binary'])
        tree = self.spec['tree']
        (self.repo / '.git/objects' / tree[:2] / tree[2:]).unlink()
        absent = subprocess.run(['git', '-C', str(self.repo), 'cat-file', '-e', tree],
                                capture_output=True)
        self.assertNotEqual(absent.returncode, 0)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); profile = root / 'profile'; profile.mkdir()
            patch_path = profile / 'change.patch'; patch_path.write_bytes(patch_bytes)
            specification = dict(self.spec, url='https://github.com/proofs-rs/proofs-rs.git',
                patches=[{'file': 'change.patch', 'sha256': tools.digest(patch_path)}])
            checkout = root / 'new-checkout'
            with patch.dict(os.environ, {'AENEAS_PROOFS_RS_CACHE': str(self.repo)}):
                with (root / 'setup.log').open('wb') as log:
                    tools.restore_repository(checkout, specification, profile, log, offline=True)
            self.assertEqual((checkout / 'source').read_bytes(), b'patched\n')
            subprocess.run(['git', '-C', str(checkout), 'cat-file', '-e', tree], check=True)
            # After restoration, even a held index lock cannot affect validation.
            (checkout / '.git/index.lock').write_text('another operation owns this lock')
            tools.source_check(checkout, specification)

    def test_staged_tree_drift_rejected(self):
        (self.repo / 'source').write_text('changed staged body\n')
        self.git('add', 'source')
        with self.assertRaisesRegex(ValueError, 'patched index'):
            tools.source_check(self.repo, self.spec)

    def test_unstaged_body_drift_rejected(self):
        (self.repo / 'source').write_text('changed working body\n')
        with self.assertRaisesRegex(ValueError, 'blob changed'):
            tools.source_check(self.repo, self.spec)

    def test_assume_unchanged_does_not_hide_modified_source(self):
        self.git('update-index', '--assume-unchanged', 'source')
        (self.repo / 'source').write_text('hidden modified body\n')
        with self.assertRaisesRegex(ValueError, 'blob changed'):
            tools.source_check(self.repo, self.spec)

    def test_skip_worktree_does_not_hide_modified_source(self):
        self.git('update-index', '--skip-worktree', 'source')
        (self.repo / 'source').write_text('hidden modified body\n')
        with self.assertRaisesRegex(ValueError, 'blob changed'):
            tools.source_check(self.repo, self.spec)

    def test_filemode_config_cannot_hide_mode_drift(self):
        self.git('config', 'core.fileMode', 'false')
        source = self.repo / 'source'
        source.chmod(source.stat().st_mode | 0o111)
        with self.assertRaisesRegex(ValueError, 'executable mode'):
            tools.source_check(self.repo, self.spec)

    def test_symlink_blob_checked_without_following_target(self):
        link = self.repo / 'link'
        link.symlink_to('source')
        self.git('add', 'link')
        self.spec['tree'] = self.git('write-tree')
        tools.source_check(self.repo, self.spec)
        self.git('update-index', '--skip-worktree', 'link')
        link.unlink(); link.symlink_to('other-source')
        with self.assertRaisesRegex(ValueError, 'blob changed'):
            tools.source_check(self.repo, self.spec)

    def test_nested_parent_symlink_rejected_even_with_matching_bytes(self):
        directory = self.repo / 'directory'; directory.mkdir()
        (directory / 'file').write_text('same bytes\n')
        self.git('add', 'directory/file')
        self.spec['tree'] = self.git('write-tree')
        self.git('update-index', '--skip-worktree', 'directory/file')
        saved = self.repo / '.git/saved-directory'
        directory.rename(saved); directory.symlink_to(saved, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'parent became a symlink'):
            tools.source_check(self.repo, self.spec)

    def test_independently_patched_gitlink_is_not_rejected_as_parent_drift(self):
        nested = self.repo / 'vendor'; nested.mkdir()
        def git(*args):
            return subprocess.check_output(['git', '-C', str(nested), *args], stderr=subprocess.PIPE).decode().strip()
        git('init', '-q'); git('config', 'user.name', 'Test')
        git('config', 'user.email', 'test@example.invalid')
        (nested / 'file').write_text('nested base\n'); git('add', 'file'); git('commit', '-qm', 'base')
        commit = git('rev-parse', 'HEAD')
        self.git('update-index', '--add', '--cacheinfo', '160000,' + commit + ',vendor')
        self.spec['tree'] = self.git('write-tree')
        (nested / 'file').write_text('independently locked patch\n'); git('add', 'file')
        tools.source_check(self.repo, self.spec)
        self.git('update-index', '--cacheinfo', '160000,' + self.spec['revision'] + ',vendor')
        with self.assertRaisesRegex(ValueError, 'patched index'):
            tools.source_check(self.repo, self.spec)

    def test_untracked_source_rejected(self):
        (self.repo / 'extra').write_text('new source\n')
        with self.assertRaisesRegex(ValueError, 'Untracked'):
            tools.source_check(self.repo, self.spec)

    def test_wrong_origin_rejected(self):
        self.git('remote', 'set-url', 'origin', 'https://example.invalid/other.git')
        with self.assertRaisesRegex(ValueError, 'origin'):
            tools.source_check(self.repo, self.spec)


class ReceiptBinding(unittest.TestCase):
    def test_misplaced_receipt_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            store = Path(directory) / 'new-store'; store.mkdir()
            lock = {'repositories': {}}
            (store / 'receipt.json').write_text(json.dumps({'identity': 'old-store', 'inputs': lock}))
            with self.assertRaisesRegex(ValueError, 'cache identity'):
                tools.check(store, lock)

    def test_stale_receipt_inputs_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            store = Path(directory) / 'store'; store.mkdir()
            lock = {'repositories': {}, 'native_rust': 'fixed'}
            (store / 'receipt.json').write_text(json.dumps({'identity': 'store',
                'inputs': dict(lock, native_rust='old')}))
            with self.assertRaisesRegex(ValueError, 'receipt inputs'):
                tools.check(store, lock)
            (store / 'receipt.json').write_text(json.dumps({'identity': 'store', 'inputs': lock,
                                                          'binaries': {}}))
            with patch.object(tools, 'paths', return_value={}):
                self.assertEqual(tools.check(store, lock)['inputs'], lock)


class RecipeCompatibility(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        implementation = Path(tools.__file__).resolve().parent
        for name in ('tools.py', 'recipe-compatibility.json'):
            shutil.copyfile(implementation / name, self.root / name)
        self.original_file = tools.__file__
        tools.__file__ = str(self.root / 'tools.py')
        self.current = {'recipe_sha256': tools.digest(tools.__file__),
                        'host': 'test-host', 'cc': 'test compiler',
                        'sdk': 'test-sdk', 'flags': {'CFLAGS': None}}
        self.old_hash = OLD_RECIPE_SHA256
        self.previous = dict(self.current, recipe_sha256=self.old_hash)

    def tearDown(self):
        tools.__file__ = self.original_file
        self.temp.cleanup()

    def test_exact_reviewed_transition_and_donor_provenance(self):
        record = tools.compiler_context_compatibility(self.previous, self.current)
        self.assertEqual(record['kind'], 'reviewed-recipe-transition')
        donor = self.root / 'old-store/receipt.json'
        donor.parent.mkdir()
        donor.write_text(json.dumps({'build_context': self.previous}))
        before = donor.read_bytes()
        result = tools.compiler_reuse_record(donor, record, ['aeneas', 'charon'])
        self.assertEqual(result['receipt_sha256'], hashlib.sha256(before).hexdigest())
        self.assertEqual(result['previous_recipe_sha256'], self.old_hash)
        self.assertEqual(result['current_recipe_sha256'], self.current['recipe_sha256'])
        self.assertEqual(donor.read_bytes(), before)

    def test_changed_build_conditions_and_missing_context_rejected(self):
        self.assertIsNone(tools.compiler_context_compatibility(None, self.current))
        for key, value in [('host', 'other'), ('sdk', 'other'), ('cc', 'other'),
                           ('flags', {'CFLAGS': '-DOTHER'})]:
            with self.subTest(key=key):
                self.assertIsNone(tools.compiler_context_compatibility(dict(self.previous, **{key: value}), self.current))
        self.assertIsNone(tools.compiler_context_compatibility(dict(self.previous, recipe_sha256='0' * 64), self.current))

    def test_wrong_new_recipe_mapping_rejected(self):
        path = self.root / 'recipe-compatibility.json'
        mapping = json.loads(path.read_text())
        mapping['compiler_reuse'][self.old_hash]['current_recipe_sha256'] = '0' * 64
        path.write_text(json.dumps(mapping))
        self.assertIsNone(tools.compiler_context_compatibility(self.previous, self.current))

    def test_future_code_edit_rejected_until_explicit_review(self):
        Path(tools.__file__).write_text(Path(tools.__file__).read_text() + '\n# future change\n')
        new_context = dict(self.current, recipe_sha256=tools.digest(tools.__file__))
        self.assertIsNone(tools.compiler_context_compatibility(self.previous, new_context))
        self.assertIsNone(tools.compiler_context_compatibility(self.previous, self.current))

    def test_mapping_is_in_cache_identity(self):
        profile = self.root / 'profile'
        profile.mkdir()
        (profile / 'opam.locked').write_text('fixed')
        (profile / 'toolchain.lock.json').write_text(json.dumps({'schema_version': 1,
            'recipe': 'aeneas-opam-v1', 'opam_sha256': tools.digest(profile / 'opam.locked'),
            'repositories': {}}))
        with patch.object(tools, 'build_context', return_value=self.current):
            _, first = tools.identity(profile)
            path = self.root / 'recipe-compatibility.json'
            mapping = json.loads(path.read_text())
            mapping['compiler_reuse'][self.old_hash]['reason'] += ' reviewed'
            path.write_text(json.dumps(mapping))
            _, second = tools.identity(profile)
        self.assertNotEqual(first, second)

    def test_missing_mapping_fails_closed(self):
        (self.root / 'recipe-compatibility.json').unlink()
        with self.assertRaises(FileNotFoundError):
            tools.compiler_context_compatibility(self.previous, self.current)
        profile = self.root / 'profile'
        profile.mkdir()
        (profile / 'opam.locked').write_text('fixed')
        (profile / 'toolchain.lock.json').write_text(json.dumps({'schema_version': 1,
            'recipe': 'aeneas-opam-v1', 'opam_sha256': tools.digest(profile / 'opam.locked'),
            'repositories': {}}))
        with patch.object(tools, 'build_context', return_value=self.current):
            with self.assertRaises(FileNotFoundError):
                tools.identity(profile)


if __name__ == '__main__':
    unittest.main()
