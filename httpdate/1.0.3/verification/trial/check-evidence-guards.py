#!/usr/bin/env python3
"""Try corrupted copies of a successful run; require refusal and unchanged evidence."""
import datetime
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

VERSION = Path(__file__).resolve().parents[2]
CHECKER = VERSION / 'scripts/check-proofs.py'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def evidence_hashes():
    root = VERSION / 'verification/evidence/latest'
    return {str(path.relative_to(root)): sha(path) for path in sorted(root.rglob('*')) if path.is_file()}


def main():
    source_run = Path(sys.argv[1]).resolve()
    targets = subprocess.check_output(['python3', str(CHECKER), '--targets'], cwd=VERSION, text=True).splitlines()
    if not targets:
        raise ValueError('No expected targets')
    original = evidence_hashes()
    outcomes = []
    open_targets = subprocess.check_output(['python3', str(CHECKER), '--open-targets'], cwd=VERSION, text=True).splitlines()
    cases = ('changed_input', 'zero_goals', 'missing_target_vc', 'open_target_goal',
             'missing_auxiliary_goal', 'unclassified_generated', 'missing_generated', 'unexpected_open_goal',
             'closed_expected_open', 'missing_open_target_vc', 'abnormal_open_exit')
    with tempfile.TemporaryDirectory(prefix='httpdate-evidence-guards-') as directory:
        for case in cases:
            run = Path(directory) / case
            shutil.copytree(source_run, run)
            base = run / 'coma/verif/httpdate_rlib'
            proof_file = base / targets[0] / 'proof.json'
            if case == 'changed_input':
                inputs_file = run / 'inputs.json'
                data = json.loads(inputs_file.read_text())
                data[next(iter(data))] = '0' * 64
                inputs_file.write_text(json.dumps(data))
            elif case == 'unclassified_generated':
                (base / 'unexpected.coma').write_text('goal vc_unexpected: true\n')
            elif case == 'missing_generated':
                (base / (targets[0] + '.coma')).unlink()
            elif case == 'abnormal_open_exit':
                (run / 'open-prove.exit').write_text('124\n')
            else:
                if case in ('unexpected_open_goal', 'closed_expected_open', 'missing_open_target_vc'):
                    proof_file = base / open_targets[0] / 'proof.json'
                data = json.loads(proof_file.read_text())
                if case == 'zero_goals':
                    data['proofs'] = {}
                elif case == 'missing_auxiliary_goal':
                    expected = 'vc_' + targets[0].rsplit('/', 1)[-1]
                    removed = False
                    for group in data['proofs'].values():
                        other = next((name for name in group if name != expected), None)
                        if other is not None:
                            del group[other]
                            removed = True
                            break
                    if not removed:
                        raise ValueError('Reference first session has no auxiliary goal')
                elif case == 'unexpected_open_goal':
                    next(iter(data['proofs'].values()))['vc_unexpected'] = {}
                else:
                    expected = ('refines' if case in ('closed_expected_open', 'missing_open_target_vc')
                                else 'vc_' + targets[0].rsplit('/', 1)[-1])
                    found = False
                    for group in data['proofs'].values():
                        if expected in group:
                            if case in ('missing_target_vc', 'missing_open_target_vc'):
                                del group[expected]
                            elif case == 'closed_expected_open':
                                group[expected] = {'prover': 'fake-for-guard', 'time': 0.0}
                            else:
                                group[expected] = {}
                            found = True
                    if not found:
                        raise ValueError('Fresh reference run did not contain target VC')
                proof_file.write_text(json.dumps(data))
            result = subprocess.run(['python3', str(CHECKER), str(run)], cwd=VERSION, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            unchanged = evidence_hashes() == original
            outcomes.append({'case': case, 'exit': result.returncode, 'evidence_unchanged': unchanged,
                             'output': result.stdout})
            if result.returncode == 0 or not unchanged:
                raise ValueError(f'Corrupted evidence accepted or latest modified: {case}')
    summary = {'generated_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
               'reference_run': str(source_run.relative_to(VERSION)),
               'checker_sha256': sha(CHECKER), 'guard_runner_sha256': sha(Path(__file__)),
               'reference_manifest_sha256': original['manifest.json'], 'cases': outcomes}
    output = VERSION / 'verification/trial/evidence-guards.json'
    output.write_text(json.dumps(summary, indent=2) + '\n')
    print(f'{len(cases)} corrupted-run cases rejected; latest evidence unchanged.')


if __name__ == '__main__':
    main()
