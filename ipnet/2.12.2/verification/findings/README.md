# Findings inventory

Migrated records follow the shared template. Original records, reproducers and
evidence are unchanged; no latest-upstream check is implied. Current Rust-only
reproductions are in [the report draft](../../aeneas/profiles/default/proofs.toml);
the records below preserve historical observations and their archive identities.

| ID | Kind | Observation |
| --- | --- | --- |
| [IPNET-001](IPNET-001.md) | implementation-bug | IpNet schema rejects valid serialized IPv4 networks |
| [IPNET-002](IPNET-002.md) | implementation-bug | IPv6 and IpNet schemas accept strings deserialization rejects |
| [IPNET-003](IPNET-003.md) | implementation-bug | Heapless feature misses stack-buffer serialization |
| [IPNET-004](IPNET-004.md) | specification-question | Raw subnet constructors defer invalid-prefix failure |

Do not count unsupported extraction, out-of-domain inputs or repeated profiles as
new implementation bugs. Use the [shared template](../../../../verification/templates/finding.md) for new findings.
