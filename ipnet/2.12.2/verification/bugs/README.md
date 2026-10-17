# Findings for later upstream PRs — ipnet 2.12.2

No issue or PR has been published. The unchanged release at commit
`13c5c5873c02127679b1e8e64b538e4e36942640` is the reproduction target.
These are native counterexamples, separate from the Lean theorem inventory.
The user-supplied expert review identified the schema issue; this investigation
confirmed it end-to-end against Rust-generated schemas and actual serde output.

## IPNET-001 — IpNet schema rejects valid serialized IPv4 networks

**Status: reproduced, upstream PR candidate.** Affects both `schemars08` (0.8.22)
and `schemars1` (1.2.1) integrations in ipnet 2.12.2.

Expected: for an `IpNet` value, its serialized JSON satisfies its generated schema.
Actual: `192.168.0.0/24` and `0.0.0.0/0` parse and serialize successfully, but the
`IpNet` schema rejects the emitted JSON strings. Each string matches both branches
of `oneOf`: the IPv4 branch and the overly broad IPv6 pattern. `oneOf` requires
exactly one successful branch. The IPv6 control `fd00::/32` passes.

Affected implementation:
- `upstream/src/ipnet_schemars_08.rs`: IPv6 `pattern`, and `IpNet::json_schema` oneOf.
- `upstream/src/ipnet_schemars_1.rs`: same pattern and combination.

Potential patch direction: make family schemas disjoint, preserving valid IPv6
including embedded IPv4 forms. Switching only `oneOf` to `anyOf` would address
this output-rejection example, but leave the IPv6 schema unsound against parsing.
No patch is proposed as proved correct here; full IPv6 grammar and parser
acceptance policy need review. Add output-conformance regression tests for both
schema versions, IPv4 boundary prefixes, compressed/uncompressed IPv6, and embedded IPv4.

## IPNET-002 — IPv6/IpNet schema accepts strings rejected by deserialization

**Status: reproduced schema/Deserialize defect, supported by the published Serde-compatibility goal and ipnet integration history.**
Both generated IPv6 and generic schemas accept `a/64`, while actual
`serde_json::from_value::<Ipv6Net>` and `::<IpNet>` reject it. The same IPv6 schema
also accepts IPv4-only strings which IPv6 deserialization rejects.

Official Schemars documentation and ipnet issue #40 / merged PR #41 support
Serde/parser correspondence as the intended behavior. We therefore classify
this as a schema defect, distinct from IPNET-001's output-conformance failure.
No explicit universal iff guarantee or maintainer ruling on this exact example
was found. See [source-backed review](../issue-repros/upstream-review.md).

## Reproduction

Regenerate all three finding packages and their maintained logs with
`python3 verification/bugs/refresh.py` from the version directory after
`source scripts/env.sh`. It uses a fresh ignored Cargo target directory and
updates each package's hashed `evidence.json`. The commands below show the
schema case separately.

From repository root:

```bash
source ipnet/2.12.2/scripts/env.sh
cargo run --locked --manifest-path ipnet/2.12.2/verification/bugs/schema-repro/Cargo.toml \
  > ipnet/2.12.2/verification/bugs/schema-repro/generated.json
python3 -m venv ipnet/2.12.2/.tools/schema-python
ipnet/2.12.2/.tools/schema-python/bin/python -m pip install \
  -r ipnet/2.12.2/verification/bugs/schema-repro/requirements.txt
ipnet/2.12.2/.tools/schema-python/bin/python \
  ipnet/2.12.2/verification/bugs/schema-repro/check.py
```

`check.py` exits successfully only when the recorded counterexamples reproduce.
For a future PR regression test, `check.py --expect-fixed` asserts output
conformance and currently fails on the first IPv4 example. Neither mode copies
upstream regexes into a simulated schema: `generated.json` comes from actual
`schema_for!` calls, and validation uses Python jsonschema 4.25.1 with the draft
specified by each emitted schema. Rust and Python dependencies are pinned in
separate Cargo.lock and requirements.txt files. The original crate manifest and
lockfile are unchanged.

Saved evidence: `schema-repro/generated.json`, `schema-repro/result.json`, and
`schema-repro/evidence.json`. The isolated reproduction package is not part of
the formal proof workspace. No failure in the CIDR set regression tests has
been observed in this investigation; finite tests do not establish correctness.


## Known raw-subnet prefix domain (not a new algorithm bug)

A fresh native confirmation of the previously specified q>32/nonempty panic
is saved in [subnets-domain-repro](subnets-domain-repro/README.md). This is a
possible documentation/validation API improvement, not a counterexample for
valid prefixes and not a newly discovered bug. The expert review and earlier
set-operations specification already classify this panic domain. No upstream
issue or PR was published.


## IPNET-003 — documented heapless feature still allocates during serialization

**Status: new bug confirmed by native reproduction and independent rerun.**
Enabling `heapless` alone does not select the stack-buffer serializer because
that branch is guarded only by legacy `ser_as_str`. With the same locked serde
serializer and the same IPv4 network, heapless-only performs 3 allocations or
reallocations while legacy serde+ser_as_str performs zero; both produce exactly
`255.255.255.255/32`. The serializer's own serialize_str does not allocate;
serde's inherited collect_str uses to_string. This contradicts the documented
feature's allocation-avoidance behavior for this supported serializer.

See [isolated reproduction and commands](heapless-feature-repro/README.md),
its Cargo.lock, source, captured logs and evidence.json. IPv4 is directly
reproduced. A later independent IPv6 executable confirms the same defect for
the 43-byte maximum-width representation: heapless-only allocates 4 times,
legacy zero. See heapless-feature-repro/ipv6-evidence.json. This is an extension
of the same recorded bug, not a new finding.
This is distinct from the previously known schema bugs and raw-prefix panic.
No upstream fix or publication was performed.
