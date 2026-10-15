# Verification plan: form_urlencoded 1.2.2

## Identity and provenance

- Crate / exact version: `form_urlencoded` 1.2.2.
- Registry archive SHA-256: `cb4cb245038516f5f85277875cdaa4f7d2c9a0fa0468de06ed190163b1581fcf`.
- Provenance: raw crates.io sparse-index response preserved at `verification/provenance/form_urlencoded.sparse-index.jsonl`, with URL, UTC capture date, and SHA-256 recorded in `verification/provenance/README.md`. The archive is preserved in `capture/release.crate`. Capture metadata is synthesized from the sparse-index version/checksum fields because the crates.io version API returned HTTP 403. The capture checker independently verified archive bytes against the registry checksum and extracted source hashes.
- Upstream repository / commit: `https://github.com/servo/rust-url`, commit `91377f48bf35011d042aa5abef9e7f2a0a625aaa`, path `form_urlencoded`; archive `.cargo_vcs_info.json` says `dirty: true`.
- Archive and VCS tree: distinct identities; Git tree equality has not been established.
- Capture: `form_urlencoded/1.2.2/capture`; command recorded by the task as `scripts/capture-crate-release.py form_urlencoded 1.2.2 --output form_urlencoded/1.2.2/capture --metadata-file /tmp/form-url-registry-metadata.json --archive-file /tmp/form_urlencoded-1.2.2.crate`.
- Rust / verifier / prover versions: to record at the first fresh proof run.
- Blockers: archive VCS metadata is marked dirty; index provenance is a saved response and has not been independently refreshed in this run.

## Build surface

- Default feature: `std`; it enables `alloc` and `percent-encoding/std`. `alloc` is required by the library source. `no_std` crate with `alloc`.
- Optional features: `alloc`, `std`.
- Public API: `parse`, `Parse`, `ParseIntoOwned`, `byte_serialize`, `ByteSerialize`, `Serializer`, `Target`, `EncodingOverride`.
- MSRV: 1.51. Main dependency requirement: `percent-encoding` `^2.3.0`, default features disabled; workspace lock resolves 2.3.2 (checksum `9b4f627cb1b25917193a259e49bdad08f671f8d9708acfd5fe0a8c1455d87220`).
- Build script / proc macros / async / FFI: none in normalized release manifest.
- Unsafe: serializer uses `str::from_utf8_unchecked`; lossy decode has pointer check and `String::from_utf8_unchecked`.
- Selected byte core: `byte_serialized_unchanged`, exhaustive `percent_encoded_bytes`, raw pair bounds, first-plus search, and in-place plus replacement. `ByteSerialize::next` uses the checked byte helper at runtime, while its iterator/string wrapper remains formally excluded.
- Deferred boundaries: `percent_decode`, `String::from_utf8_lossy`, arbitrary `EncodingOverride` callbacks, allocation/Cow ownership, `Target`, and serializer mutation/panic state.

## Contracts and scope

| API / helper | Intended contract | Status |
| --- | --- | --- |
| `byte_serialized_unchanged` | True exactly for `*`, `-`, `.`, ASCII digits, uppercase/lowercase letters, `_`; this set is valid UTF-8. | Selected; fresh proof bundle records status |
| `percent_encoded_bytes` | For each `u8`, return `%` and uppercase hexadecimal digits for its high and low nibbles. | Selected; all 256 match arms are checked |
| raw pair bounds | Identify the first nonempty segment, its first `=`, segment end, and next suffix boundary. | Selected; public Parse iterator wrapper remains excluded |
| `find_plus` / `replace_plus_in_place` | Return first plus or absence; replace every plus with space without changing length or other bytes. | Selected helpers; Cow wrapper ownership excluded |
| `decode` | Uses plus mapping, external percent decoding, then lossy UTF-8 conversion. | Excluded pending dependency and std models |

- Feature / target selection: default `std` feature on the configured Creusot target; exact target to record with run.
- Explicit exclusions: full public parser decoded-string semantics, malformed percent behavior, lossy UTF-8, serializer API, callback and target semantics, whole-crate guarantee.
- Runtime correspondence: the release implementation remains the reference. The fork may add contracts or refactor core helpers to make their behavior specifiable; record each runtime change and explain how it preserves release behavior. Pair such changes with native differential observations when feasible.

## Trust and correspondence

| Boundary | Domain | Evidence / limitation |
| --- | --- | --- |
| `percent-encoding` | `percent_decode` and `percent_encode_byte` calls | External dependency contract not yet modeled; no application algorithm may be trusted. |
| UTF-8 lossy conversion | arbitrary byte sequences | Standard-library behavior not modeled; excluded. |
| `EncodingOverride` | caller callback | Arbitrary transformation/panic; excluded. |

## Evidence and decision

- `scripts/verify.sh` creates a unique run directory, snapshots source/dependency/tool inputs, runs finite native differential checks, translates fresh Coma, proves the selected files without cache, packages logs and sessions, and runs the repository evidence auditor.
- Native finite differential observations are separate evidence and are not an all-input equivalence proof.
- Verification claims apply only to the selected helper contracts. The public iterator wrappers and decoded parsing/serialization boundaries remain excluded.
