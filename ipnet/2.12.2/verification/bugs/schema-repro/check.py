#!/usr/bin/env python3
"""Validate schemas emitted by the unchanged ipnet release, not copied regexes."""
import argparse
import importlib.metadata
import json
from pathlib import Path
import jsonschema

parser = argparse.ArgumentParser()
parser.add_argument('--expect-fixed', action='store_true', help='Fail on the output-conformance bug (future PR regression mode).')
args = parser.parse_args()
root = Path(__file__).resolve().parent
data = json.loads((root/'generated.json').read_text())
rows = []
for version in ('schemars08', 'schemars1'):
    schemas = data[version]
    validators = {}
    for name, schema in schemas.items():
        cls = jsonschema.validators.validator_for(schema)
        cls.check_schema(schema)
        validators[name] = cls(schema)
    for sample in data['samples']:
        value = sample['serialized'] if sample['ipnet_parses'] else sample['input']
        validity = {name: v.is_valid(value) for name, v in validators.items()}
        row = {'feature': version, 'value': value, **validity,
               'ipnet_parses': sample['ipnet_parses'], 'ipv6_parses': sample['ipv6_parses'],
               'ipnet_deserializes': sample['ipnet_deserializes'],
               'ipv6_deserializes': sample['ipv6_deserializes']}
        rows.append(row)
        if args.expect_fixed and sample['ipnet_parses']:
            assert validity['IpNet'], f'Output conformance violated: {row}'
        if not args.expect_fixed:
            expected = {'192.168.0.0/24': (True, True, False),
                        '0.0.0.0/0': (True, True, False),
                        'fd00::/32': (False, True, True),
                        'a/64': (False, True, True)}[value]
            assert tuple(validity[t] for t in ('Ipv4Net', 'Ipv6Net', 'IpNet')) == expected, row
            assert sample['ipnet_parses'] == sample['ipnet_deserializes'] == (value != 'a/64')
            assert sample['ipv6_parses'] == sample['ipv6_deserializes'] == (value == 'fd00::/32')
result = {'status': 'counterexamples-reproduced',
          'jsonschema_version': importlib.metadata.version('jsonschema'),
          'rows': rows,
          'scope': 'Native counterexamples against generated schemas; not formal proof.'}
print(json.dumps(result, indent=2))
