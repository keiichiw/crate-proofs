# Findings

| Local reference | Finding | Related APIs |
| --- | --- | --- |
| [BYTES-001](BYTES-001.md) | Checked signed reads omit sign extension | `bytes::Buf::try_get_int`, `bytes::Buf::try_get_int_le`, `bytes::Buf::try_get_int_ne` |

Author the public title, Markdown body and API paths in
[report.findings](../../aeneas/profiles/default/proofs.toml). BYTES-001 is a local
reference, not a server-assigned Finding ID. The native reproduction and original
review are separate from successful Claim/theorem records. Extraction limitations
and proof exclusions belong in the report scope, not duplicate bug entries.
