import json, sys
from jsonschema.validators import validator_for
x = json.load(sys.stdin)
for version in ('v08', 'v1'):
    def accepts(kind, value):
        schema = x[version][kind]
        cls = validator_for(schema)
        cls.check_schema(schema)
        return cls(schema).is_valid(value)
    assert not accepts('net', x['valid_value'])
    assert accepts('v6', x['invalid_value'])
    print(version, 'IPNET-001: valid serialized 0.0.0.0/0 rejected; '
          'IPNET-002: invalid a/64 accepted')
