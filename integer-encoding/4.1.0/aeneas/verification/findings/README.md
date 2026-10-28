# Findings inventory

Migrated records follow the shared template. Original records, reproducers and
evidence are unchanged; no reproduction or latest-upstream check was performed.

| ID | Kind | Observation |
| --- | --- | --- |
| [IE-S1](IE-S1.md) | implementation-bug | Varint stream width cap leaves a complete value partially consumed |
| [IE-S2](IE-S2.md) | documentation-mismatch | Complete numeric overflow is reported as UnexpectedEof |
| [IE-G1](IE-G1.md) | implementation-bug | Generic FixedInt I/O has an undocumented eight-byte capacity limit |
| [IE-D1](IE-D1.md) | documentation-mismatch | FixedInt exact-length requirement is incompletely documented |
| [IE-D2](IE-D2.md) | documentation-mismatch | FixedInt overview and method endian descriptions disagree |

Do not count unsupported extraction, out-of-domain inputs or repeated profiles as
new implementation bugs. Use the [shared template](../../../../../verification/templates/finding.md) for new findings.
