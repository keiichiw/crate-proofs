"""Trial logs are execution records and diagnostic hints, never proof evidence."""

import hashlib
import json
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest


SCRIPTS = Path(__file__).resolve().parents[1]
RECORD = SCRIPTS / 'record-trial.py'
DIAGNOSE = SCRIPTS / 'diagnose-trial.py'


class TrialTools(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.output = self.root / 'trial'

    def record(self, command, extra=()):
        return subprocess.run([sys.executable, str(RECORD), '--output', str(self.output),
                               '--stage', 'compile', '--cwd', str(self.root), *extra,
                               '--', *command], capture_output=True, text=True)

    def manifest(self):
        return json.loads((self.output / 'trial.json').read_text())

    def test_success_argv_literal_and_input_hash(self):
        source = self.root / 'source.txt'
        source.write_bytes(b'input bytes\n')
        literal = 'a b;$(echo unsafe)'
        run = self.record([sys.executable, '-c', 'import sys; print(sys.argv[1])', literal],
                          ['--input', 'source.txt', '--purpose', 'literal argv'])
        self.assertEqual(run.returncode, 0, run.stderr)
        record = self.manifest()
        self.assertEqual(record['state'], 'finished')
        self.assertEqual(record['argv'][-1], literal)
        self.assertEqual((self.output / 'stdout.log').read_text().strip(), literal)
        self.assertEqual(record['inputs'][0]['sha256'], hashlib.sha256(source.read_bytes()).hexdigest())
        self.assertEqual(record['recorder_sha256'], hashlib.sha256(RECORD.read_bytes()).hexdigest())
        self.assertEqual(record['child_returncode'], 0)
        self.assertEqual(record['wrapper_exit_code'], 0)
        self.assertEqual(record['proof_status'], 'unknown')
        self.assertGreaterEqual(record['duration_seconds'], 0)

    def test_nonzero_and_existing_output(self):
        run = self.record([sys.executable, '-c', 'raise SystemExit(7)'])
        self.assertEqual(run.returncode, 7)
        self.assertEqual(self.manifest()['child_returncode'], 7)
        before = (self.output / 'trial.json').read_bytes()
        second = self.record([sys.executable, '-c', 'print("again")'])
        self.assertNotEqual(second.returncode, 0)
        self.assertEqual((self.output / 'trial.json').read_bytes(), before)

    def test_missing_executable_is_recorded(self):
        run = self.record(['missing-trial-executable-987654321'])
        self.assertEqual(run.returncode, 127)
        self.assertEqual(self.manifest()['spawn_error']['type'], 'FileNotFoundError')
        self.assertIsNone(self.manifest()['child_returncode'])
        self.assertEqual(self.manifest()['wrapper_exit_code'], 127)
        self.assertEqual(self.manifest()['proof_status'], 'unknown')

    def test_interrupt_is_recorded(self):
        command = [sys.executable, '-c', 'import time; time.sleep(30)']
        process = subprocess.Popen([sys.executable, str(RECORD), '--output', str(self.output),
                                    '--stage', 'run', '--', *command],
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            for _ in range(100):
                if (self.output / 'trial.json').exists():
                    break
                time.sleep(.02)
            self.assertTrue((self.output / 'trial.json').exists())
            process.send_signal(signal.SIGTERM)
            process.communicate(timeout=10)
            self.assertEqual(process.returncode, 128 + signal.SIGTERM)
            self.assertEqual(self.manifest()['interrupted_signal'], signal.SIGTERM)
            self.assertEqual(self.manifest()['wrapper_exit_code'], 128 + signal.SIGTERM)
            self.assertEqual(self.manifest()['child_returncode'], -signal.SIGTERM)
            self.assertEqual(self.manifest()['state'], 'finished')
        finally:
            if process.poll() is None:
                process.kill()
                process.wait()

    def test_interrupt_cleans_descendant_that_ignores_term(self):
        heartbeat = self.root / 'heartbeat'
        grandchild = ('import pathlib, signal, time; '
                      'signal.signal(signal.SIGTERM, signal.SIG_IGN); '
                      f'p=pathlib.Path({str(heartbeat)!r}); '
                      '[(p.open("ab").write(b"x"), time.sleep(.02)) for _ in range(1000)]')
        leader = ('import subprocess, sys, time; '
                  f'subprocess.Popen([sys.executable, "-c", {grandchild!r}]); '
                  'time.sleep(30)')
        process = subprocess.Popen([sys.executable, str(RECORD), '--output', str(self.output),
                                    '--stage', 'run', '--', sys.executable, '-c', leader],
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            for _ in range(200):
                if heartbeat.exists() and heartbeat.stat().st_size > 0:
                    break
                time.sleep(.02)
            self.assertTrue(heartbeat.exists())
            process.send_signal(signal.SIGTERM)
            process.communicate(timeout=10)
            self.assertEqual(process.returncode, 128 + signal.SIGTERM)
            size = heartbeat.stat().st_size
            time.sleep(.2)
            self.assertEqual(heartbeat.stat().st_size, size)
        finally:
            if process.poll() is None:
                process.kill()
                process.wait()

    def test_diagnosis_positive_and_false_positives(self):
        log = self.root / 'compiler.log'
        log.write_text('before\nerror[E0308]: mismatched types\n'
                       'Foo.lean:2:3: error: tactic failed\n'
                       '[Error ] extraction failed\n'
                       'Traceback (most recent call last):\n'
                       'ValueError: bad value\nError: 1 unproved file\n'
                       'Aesop.Exception: error\nBatteries.Tactic.Unreachable\n'
                       '/tmp/sol-prefix-error-derived.lean:7:8: information: error message\n')
        result = subprocess.run([sys.executable, str(DIAGNOSE), '--stage', 'probe', str(log)],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(result.stdout)
        self.assertEqual(report['proof_status'], 'unknown')
        self.assertEqual(report['symptom_status'], 'observed')
        self.assertEqual(report['counts'], {'aeneas': 1, 'lean': 1, 'python': 2,
                                            'rust': 1, 'why3': 1})
        self.assertEqual(report['logs'][0]['sha256'], hashlib.sha256(log.read_bytes()).hexdigest())
        self.assertEqual(report['logs'][0]['observations'][0]['context_before'], ['before'])

    def test_real_aeneas_color_prefix_and_generic_error(self):
        log = self.root / 'aeneas.log'
        log.write_text('\x1b[?25h[\x1b[91mError\x1b[39m] Unsupported cast to a dynamic trait\n'
                       'error: plain tool failure\nError: another tool failure\n')
        result = subprocess.run([sys.executable, str(DIAGNOSE), '--stage', 'aeneas', str(log)],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)['counts'], {'aeneas': 1, 'tool-error': 2})

    def test_no_diagnostics_means_unknown(self):
        log = self.root / 'quiet.log'
        log.write_text('Aesop.Exception\nBatteries.Tactic.Unreachable\n'
                       '/tmp/sol-prefix-error-derived.lean:1:1: information: okay\n')
        result = subprocess.run([sys.executable, str(DIAGNOSE), '--stage', 'proof', str(log)],
                                capture_output=True, text=True)
        report = json.loads(result.stdout)
        self.assertEqual(report['symptom_status'], 'unknown')
        self.assertEqual(report['counts'], {})


if __name__ == '__main__':
    unittest.main()
