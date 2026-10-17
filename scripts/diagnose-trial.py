#!/usr/bin/env python3
"""Read logs and report observed diagnostics; no proof verdict is inferred."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re


ANSI = re.compile(r'\x1b\[[0-?]*[ -/]*[@-~]')
PATTERNS = (
    ('rust', re.compile(r'^error\[[A-Z][0-9]{4}\]:\s+\S')),
    ('lean', re.compile(r'^.+\.lean:\d+:\d+: error:\s+\S')),
    ('aeneas', re.compile(r'^\[Error\s*\]\s+\S')),
    ('python', re.compile(r'^(?:Traceback \(most recent call last\):|(?:[A-Za-z_][A-Za-z_0-9]*Error|Exception|KeyboardInterrupt|SystemExit):\s*\S).*')),
    ('why3', re.compile(r"^Error: (?:\d+ unproved files?|['\"]why3find prove['\"] failed)\b")),
    ('tool-error', re.compile(r'^(?:error|Error|ERROR):\s+\S')),
)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def diagnose(stage, paths, context=1):
    reports = []
    total = Counter()
    for path in paths:
        data = path.read_bytes()
        lines = data.decode('utf-8', errors='replace').splitlines()
        observations = []
        for index, line in enumerate(lines):
            clean = ANSI.sub('', line)
            for kind, pattern in PATTERNS:
                if pattern.match(clean):
                    observations.append({
                        'kind': kind, 'line': index + 1, 'text': line,
                        'context_before': lines[max(0, index - context):index],
                        'context_after': lines[index + 1:index + 1 + context],
                    })
                    total[kind] += 1
                    break
        reports.append({'path': str(path.resolve()), 'sha256': sha256(data),
                        'line_count': len(lines), 'observations': observations})
    return {'schema_version': 1, 'stage': stage, 'proof_status': 'unknown',
            'symptom_status': 'observed' if total else 'unknown',
            'counts': dict(sorted(total.items())), 'logs': reports}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stage', required=True)
    parser.add_argument('--context', type=int, default=1)
    parser.add_argument('files', type=Path, nargs='+')
    args = parser.parse_args()
    if args.context < 0:
        parser.error('--context must be nonnegative')
    for path in args.files:
        if not path.is_file():
            parser.error(f'log is not a file: {path}')
    print(json.dumps(diagnose(args.stage, args.files, args.context), indent=2,
                     ensure_ascii=False))


if __name__ == '__main__':
    main()
