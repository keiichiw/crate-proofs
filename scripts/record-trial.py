#!/usr/bin/env python3
"""Record one command trial. A successful process exit is not a proof result."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as source:
        for block in iter(lambda: source.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def utc_now():
    return datetime.now(timezone.utc).isoformat().replace('+00:00', 'Z')


def save(path, record):
    temporary = path.with_name(path.name + '.tmp')
    with temporary.open('x', encoding='utf-8') as stream:
        json.dump(record, stream, indent=2, ensure_ascii=False)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(path)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path, help='new trial directory')
    parser.add_argument('--stage', required=True)
    parser.add_argument('--cwd', type=Path, default=Path.cwd())
    parser.add_argument('--input', action='append', type=Path, default=[])
    parser.add_argument('--purpose')
    parser.add_argument('--parent-trial')
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    if not args.command or args.command[0] != '--' or len(args.command) == 1:
        parser.error('provide -- COMMAND [ARG ...]')
    command = args.command[1:]
    cwd = args.cwd.resolve(strict=True)
    if not cwd.is_dir():
        parser.error('--cwd must be a directory')
    inputs = []
    for item in args.input:
        path = (cwd / item).resolve(strict=True)
        if not path.is_file():
            parser.error(f'--input must be a file: {item}')
        inputs.append({'path': str(path), 'sha256': digest(path)})
    output = args.output.absolute()
    try:
        output.mkdir(parents=True, exist_ok=False)
    except FileExistsError:
        parser.error(f'output already exists: {output}')
    started = time.monotonic()
    record = {
        'schema_version': 1, 'trial_id': output.name, 'stage': args.stage,
        'purpose': args.purpose, 'parent_trial': args.parent_trial,
        'argv': command, 'cwd': str(cwd), 'started_utc': utc_now(),
        'inputs': inputs, 'recorder_sha256': digest(Path(__file__).resolve()),
        'stdout_log': 'stdout.log', 'stderr_log': 'stderr.log',
        'state': 'running', 'child_returncode': None, 'wrapper_exit_code': None,
        'process_status': 'unknown',
        'proof_status': 'unknown',
    }
    save(output / 'trial.json', record)
    interrupted = [None]
    child = [None]

    def on_signal(number, _frame):
        if interrupted[0] is None:
            interrupted[0] = number
        if child[0] is not None and child[0].poll() is None:
            try:
                os.killpg(child[0].pid, number)
            except ProcessLookupError:
                pass

    old_handlers = {number: signal.signal(number, on_signal)
                    for number in (signal.SIGINT, signal.SIGTERM)}
    exit_code = 127
    child_returncode = None
    try:
        with (output / 'stdout.log').open('wb') as stdout, (output / 'stderr.log').open('wb') as stderr:
            try:
                child[0] = subprocess.Popen(command, cwd=cwd, stdout=stdout, stderr=stderr,
                                            start_new_session=True)
                if interrupted[0] is not None:
                    on_signal(interrupted[0], None)
                deadline = None
                while True:
                    if interrupted[0] is not None and deadline is None:
                        deadline = time.monotonic() + 5
                    try:
                        child_returncode = child[0].wait(timeout=0.1)
                        exit_code = (128 - child_returncode if child_returncode < 0
                                     else child_returncode)
                        break
                    except subprocess.TimeoutExpired:
                        if deadline is not None and time.monotonic() >= deadline:
                            try:
                                os.killpg(child[0].pid, signal.SIGKILL)
                            except ProcessLookupError:
                                pass
                            child_returncode = child[0].wait()
                            exit_code = 128 + interrupted[0]
                            break
                if interrupted[0] is not None:
                    exit_code = 128 + interrupted[0]
                    # The leader may have exited while descendants ignored the signal.
                    try:
                        os.killpg(child[0].pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
            except OSError as error:
                record['spawn_error'] = {'type': type(error).__name__, 'message': str(error)}
                stderr.write((str(error) + '\n').encode('utf-8', errors='replace'))
                exit_code = 127 if isinstance(error, FileNotFoundError) else 126
    finally:
        for number, old_handler in old_handlers.items():
            signal.signal(number, old_handler)
        process_status = ('interrupted' if interrupted[0] is not None else
                          'spawn_error' if 'spawn_error' in record else
                          'success' if exit_code == 0 else 'failure')
        record.update(state='finished', ended_utc=utc_now(),
                      duration_seconds=round(time.monotonic() - started, 6),
                      child_returncode=child_returncode, wrapper_exit_code=exit_code,
                      process_status=process_status,
                      interrupted_signal=interrupted[0],
                      stdout_sha256=digest(output / 'stdout.log'),
                      stderr_sha256=digest(output / 'stderr.log'))
        save(output / 'trial.json', record)
    return exit_code


if __name__ == '__main__':
    sys.exit(main())
