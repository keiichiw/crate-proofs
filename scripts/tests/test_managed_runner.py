"""Behavioral regression tests for managed orchestration trust boundaries."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from aeneas_management import runner


class RunnerTests(unittest.TestCase):
    def test_runtime_guard_rejects_unlocked_compiler_inputs(self):
        import os
        with patch.dict(os.environ, {}, clear=True), patch.object(runner.tools, 'host', return_value='native'):
            runner.validate_runtime_environment()
            for name, value in [('RUSTC_WRAPPER','wrapper'), ('CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS','--cfg hidden'), ('CARGO_BUILD_TARGET','other'), ('PYTHONOPTIMIZE','1')]:
                with self.subTest(name=name), patch.dict(os.environ, {name:value}):
                    with self.assertRaises(ValueError):
                        runner.validate_runtime_environment()

    def test_runtime_identity_observes_binary_mutation_and_pinned_channels(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for name in ('rustc', 'cargo', 'lean', 'lake'):
                (root/name).write_bytes(name.encode())
            observed = []
            def output(argv, env):
                observed.append((argv, env))
                if argv[0] in ('rustup', 'elan'):
                    return str(root/argv[-1]).encode()
                return b'fixed version or cfg'
            lock = dict(native_rust='native-pin', extraction_rust='extract-pin', lean='lean-pin')
            with patch.object(runner.subprocess, 'check_output', side_effect=output), patch.object(runner.tools, 'host', return_value='native'), patch.object(runner.tools, 'build_context', return_value={'sdk':'locked-sdk'}):
                before = runner.runtime_identity(lock)
                (root/'lean').write_bytes(b'replaced binary, same version')
                after = runner.runtime_identity(lock)
            self.assertNotEqual(before['binaries']['lean']['sha256'], after['binaries']['lean']['sha256'])
            self.assertEqual(before['build_context'], {'sdk':'locked-sdk'})
            self.assertTrue(any(env.get('RUSTUP_TOOLCHAIN') == 'extract-pin' for _,env in observed))
            self.assertTrue(any(env.get('ELAN_TOOLCHAIN') == 'lean-pin' for _,env in observed))

    def test_dependency_lock_rejects_cycle(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            with patch.object(runner, 'dependencies', return_value=[(root, 'default')]):
                with self.assertRaisesRegex(ValueError, 'Cyclic'):
                    with runner.operation_lock(root, 'default'):
                        self.fail('entered cyclic graph')

    def test_operation_locks_are_ordered_and_shared_dependencies_deduplicated(self):
        from contextlib import contextmanager
        calls = []
        @contextmanager
        def take(path):
            calls.append(path)
            yield
        a,b,c = map(Path, ['/a', '/b', '/c'])
        edges = {(c,'main'):[(b,'one'),(a,'one')], (b,'one'):[(a,'one')], (a,'one'):[]}
        with patch.object(runner, 'dependencies', side_effect=lambda r,n: edges[(r,n)]), patch.object(runner.source, 'exclusive', side_effect=take):
            with runner.operation_lock(c,'main'):
                self.assertEqual(calls, [r / '.work/verify.lock' for r in (a,b,c)])

    def test_successful_preparation_does_not_mask_failed_formal_audit(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary); profile=root/'aeneas/profiles/default';profile.mkdir(parents=True)
            lean=root/'build';lean.mkdir();(lean/'lakefile.toml').write_text('name = "sample"\n')
            for f in ['inventory.json','proofs.toml']:
                (profile/f).write_text('{}')
            cfg={'supported_targets':['test-host'],'native':[], 'inventory':'inventory.json','report':'proofs.toml'}
            lock={'extraction_rust':'test'}
            def run(argv,*args):
                if len(argv)>1 and 'aeneas-audit.py' in str(argv[1]):
                    raise RuntimeError('standard audit rejected sorryAx')
            with patch.object(runner, 'configuration', return_value=(profile,cfg,{})), patch.object(runner.tools,'host',return_value='test-host'), patch.object(runner,'prepare',return_value=(root/'tools',lock,lean)), patch.object(runner.tools,'environment',return_value={}), patch.object(runner,'fingerprint',return_value={'stable':True}), patch.object(runner.tools,'run',side_effect=run):
                with self.assertRaisesRegex(RuntimeError,'audit rejected'):
                    runner.verify(root,'default')
            results=list((root/'.work/runs').glob('*/result.json'))
            self.assertEqual(len(results),1)
            self.assertEqual(json.loads(results[0].read_text())['status'],'failed')

    def test_cross_crate_dependency_changes_are_fingerprinted(self):
        import subprocess
        with tempfile.TemporaryDirectory() as temporary:
            repo=Path(temporary).resolve()
            subprocess.run(['git','init',str(repo)],check=True,capture_output=True)
            for name, deps in [('app',['dep/1:default']),('dep',[])]:
                root=repo/name/'1'; p=root/'aeneas/profiles/default';p.mkdir(parents=True)
                (root/'aeneas/profiles.toml').write_text('default="default"\n[profiles.default]\npath="aeneas/profiles/default"\ndependencies='+json.dumps(deps)+'\n')
                (p/'verification.json').write_text('{"schema_version":1}')
                (p/'Proof.lean').write_text('theorem checked : True := True.intro\n')
                (root/'.work/source').mkdir(parents=True)
                (root/'.work/source/lib.rs').write_text('pub fn f() {}')
            root=repo/'app/1';p=root/'aeneas/profiles/default'
            with patch.object(runner,'REPO',repo), patch.object(runner.tools,'host',return_value='host'), patch.object(runner.tools,'check',return_value={'checked':True}), patch.object(runner.tools,'identity',return_value=(dict(native_rust='rust',extraction_rust='rust',lean='lean'),'key')), patch.object(runner,'check_lake',return_value={}), patch.object(runner,'runtime_identity',return_value={}):
                before=runner.fingerprint(root,p,repo/'tools',dict(native_rust='rust',extraction_rust='rust',lean='lean'))
                (repo/'dep/1/aeneas/profiles/default/Proof.lean').write_text('axiom untrusted : False\n')
                after=runner.fingerprint(root,p,repo/'tools',dict(native_rust='rust',extraction_rust='rust',lean='lean'))
                self.assertNotEqual(before,after)
                self.assertIn('dep/1:default',before['dependencies'])

    def test_auxiliary_paths_cannot_escape_profile(self):
        with tempfile.TemporaryDirectory() as temporary:
            with self.assertRaises(ValueError):
                list(runner.auxiliary_tools(Path(temporary),{'auxiliary_tools':{'ordinary':'../elsewhere'}}))

    def test_auxiliary_alias_cannot_inject_environment_name(self):
        with tempfile.TemporaryDirectory() as temporary:
            with self.assertRaises(ValueError):
                list(runner.auxiliary_tools(Path(temporary),{'auxiliary_tools':{'bad-name':'ordinary'}}))

    def test_explicit_cache_reuse_does_not_replace_existing_data(self):
        import os
        with tempfile.TemporaryDirectory() as temporary:
            repo=Path(temporary).resolve();root=repo/'app/1';root.mkdir(parents=True)
            shared=repo/'shared-cache'
            with patch.object(runner,'REPO',repo), patch.dict(os.environ, {'AENEAS_TOOL_CACHE':str(shared), 'AENEAS_ARCHIVE_CACHE':str(shared/'archives')}):
                runner.shared_caches(root)
                self.assertEqual((repo/'.work/tools').resolve(), shared)
                self.assertEqual((root/'.work/cache').resolve(), shared/'archives')
                runner.shared_caches(root)
                with patch.dict(os.environ, {'AENEAS_TOOL_CACHE':str(repo/'different')}):
                    with self.assertRaisesRegex(ValueError,'existing cache'):
                        runner.shared_caches(root)
                self.assertEqual((repo/'.work/tools').resolve(), shared)

    def test_materialization_remaps_inherited_paths_and_escaped_names(self):
        with tempfile.TemporaryDirectory() as temporary:
            repo=Path(temporary).resolve();root=repo/'demo/1'
            for name, deps in [('default',[]),('stage3',['default'])]:
                p=root/'aeneas/profiles'/name/'proofs';p.mkdir(parents=True)
                (p.parent/'verification.json').write_text('{"schema_version":1}')
                (p/'lakefile.toml').write_text('name="demo-'+name+'"\n'+('[[require]]\nname="demo-default"\npath="../../default/proofs"\n' if deps else ''))
            (root/'aeneas/profiles.toml').write_text('default="default"\n[profiles.default]\npath="aeneas/profiles/default"\ndependencies=[]\n[profiles.stage3]\npath="aeneas/profiles/stage3"\ndependencies=["default"]\n')
            p=root/'aeneas/profiles/stage3';(p/'proofs/lake-manifest.json').write_text(json.dumps({'packages':[{'name':'«demo-default»','type':'path','dir':'/obsolete/default'},{'name':'aeneas','type':'path','dir':'/obsolete/backend'}]}))
            with patch.object(runner,'REPO',repo), patch.object(runner.tools,'host',return_value='host'):
                built=runner.materialize(root,'stage3',p,repo/'tools')
                packages=json.loads((built/'lake-manifest.json').read_text())['packages']
                self.assertEqual(packages[0]['name'],'«demo-default»')
                self.assertEqual(packages[0]['dir'],str(root/'.work/build/default/host/proofs'))
                self.assertEqual(packages[1]['dir'],str(repo/'tools/aeneas/backends/lean'))
                self.assertIn('name = "aeneas"',(built/'lakefile.toml').read_text())
                (p/'proofs/lakefile.toml').write_text('name="demo-stage3"\n[[require]]\nname="rogue"\npath="/external"\n')
                with self.assertRaisesRegex(ValueError,'Undeclared local'):
                    runner.materialize(root,'stage3',p,repo/'tools')

if __name__ == '__main__':
    unittest.main()

class CompositeProfiles(unittest.TestCase):
    def test_combined_result_rejects_any_failed_unit(self):
        """A passing custom/preparation step never hides a unit build/audit failure."""
        original_verify = runner.verify
        for failure in (None, 'default/second'):
            with self.subTest(failure=failure), tempfile.TemporaryDirectory() as temporary:
                root=Path(temporary)
                profile=root/'profile';profile.mkdir()
                def selected(_root,name):
                    return ['default/first','default/second'] if name=='default' else []
                visited=[]
                def child(_root,name,offline=False,prepared=None):
                    visited.append(name)
                    if name==failure:raise RuntimeError('standard Lake/audit rejected unit')
                    path=root/name;path.mkdir(parents=True)
                    (path/'result.json').write_text(json.dumps({'status':'passed'}))
                    return path
                with patch.object(runner,'units',side_effect=selected), \
                     patch.object(runner,'prepare'), \
                     patch.object(runner,'configuration',return_value=(profile,{},{})), \
                     patch.object(runner.tools,'identity',return_value=({},'tool')), \
                     patch.object(runner.tools,'host',return_value='native'), \
                     patch.object(runner,'fingerprint',return_value={'input':'fixed'}), \
                     patch.object(runner,'verify',side_effect=child):
                    if failure:
                        with self.assertRaisesRegex(RuntimeError,'Lake/audit rejected'):
                            runner.verify_units(root,'default',True)
                    else:runner.verify_units(root,'default',True)
                self.assertEqual(visited,['default/first','default/second'])
                result=json.loads(next((root/'.work/runs').glob('*/result.json')).read_text())
                self.assertEqual(result['status'],'failed' if failure else 'passed')
                self.assertEqual(len(result['units']),1 if failure else 2)

    def test_public_profile_and_internal_units_are_distinct(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary).resolve();base=root/'aeneas/profiles/default';base.mkdir(parents=True)
            (root/'aeneas/profiles.toml').write_text('default="default"\n[profiles.default]\npath="aeneas/profiles/default"\n[profiles.default.units.math]\npath="aeneas/profiles/default/subjects/math"\ndependencies=[]\n')
            (base/'verification.json').write_text('{"schema_version":1,"execution":"all-units"}')
            unit=base/'subjects/math';unit.mkdir(parents=True);(unit/'verification.json').write_text('{"schema_version":1}')
            self.assertEqual(list(runner.profiles(root)['profiles']),['default'])
            self.assertEqual(runner.units(root,'default'),['default/math'])
            self.assertEqual(runner.configuration(root,'default/math')[0],unit)
            self.assertEqual(runner.execution_name(root,unit),'default/math')
            (base/'verification.json').write_text('{"schema_version":1}')
            with self.assertRaisesRegex(ValueError,'all declared units'):
                runner.units(root,'default')
