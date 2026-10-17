# Verification plan: form_urlencoded 1.2.2

## Identity and provenance

- Crate/version: `form_urlencoded` 1.2.2; registry archive SHA-256 `cb4cb245038516f5f85277875cdaa4f7d2c9a0fa0468de06ed190163b1581fcf`.
- The raw crates.io sparse-index response and its URL, capture date, and SHA-256 are preserved under `verification/provenance/`. The registry version API returned HTTP 403; capture metadata was synthesized from the saved 1.2.2 index row. The archived release and extracted source inventory were checked against the registry checksum. See `verification/provenance/README.md`.
- Recorded VCS metadata names `https://github.com/servo/rust-url`, commit `91377f48bf35011d042aa5abef9e7f2a0a625aaa`, path `form_urlencoded`, and `dirty: true`. Archive and repository tree are distinct identities; Git-tree equality is not claimed.
- Release capture lives in `capture/`; editable fork is `crate/`. Preserve both independently.

## Build surface and dependencies

- Crate is `no_std` with `alloc`; default `std` also enables `percent-encoding/std`. Optional features are `alloc` and `std`; MSRV is 1.51.
- The release depends on `percent-encoding = ^2.3.0`; the workspace lock resolves 2.3.2 with checksum `9b4f627cb1b25917193a259e49bdad08f671f8d9708acfd5fe0a8c1455d87220`.
- Public API and trait inventory is maintained in `verification/public-api-inventory.md`. The target matrix and exact generated-target classification are in `verification/target-inventory.json`.
- Unsafe boundaries include `str::from_utf8_unchecked` in byte serialization and `String::from_utf8_unchecked` in lossy decode.

## Selected scope and current state

The requested goal is a functional guarantee of the public API, within the default `std` feature, configured Creusot target, and explicit standard-library contracts. The currently translated first-order scope comprises the parser constructors and iterator types, byte serializer constructor and iterator, and concrete `Target` implementations for `String` and `&mut String`. `Parse` and `ParseIntoOwned` have scalar-result and Cow-ownership traces. `ByteSerialize` has an exact chunk queue and size-hint contract. The exact source/target mapping is maintained in `public-api-inventory.md` and `target-inventory.json`.

Run status and the completed integrated evidence are maintained in [results.md](results.md). This plan defines proof scope; earlier diagnostic timeouts do not describe the final archived run. Edited inputs require a new complete run and matching audit.

The serializer methods that depend on the exact `EncodingOverride = dyn Fn(&str) -> Cow<[u8]>` field cannot currently translate in Creusot 0.13 (`forbidden dyn type`). Their bodies and callback behavior are therefore explicitly excluded; there is no erased or replacement callback. `ByteSerialize`'s derived Debug target is also excluded. Standard-library iterator defaults and blanket impls are accounted for through the checked concrete iterator contract plus the recorded standard-library boundary, not as separately verified library bodies.

## Trust boundary

- No application algorithm or percent-encoding algorithm may be `trusted` or assumed.
- Implement percent decoding locally and prove its exact malformed-input behavior.
- Standard-library operations may be modeled only in the separate `std_models.rs`/ledger, with exact domains and limitations. The authorized UTF-8 lossiness assumption must specify replacement semantics, borrowed/owned behavior, and byte validity conditions.
- Caller-supplied `EncodingOverride` has no proof model in the selected scope because its exact dynamic function type is unsupported. Do not assume purity, output, no panic, callback count, or side effects.
- Generic `Target` semantics must follow from checked trait contracts. Initially establish those conditions for `String` and `&mut String`; do not assume arbitrary targets are stable, append-only, or faithful.

## Validation and correspondence

`scripts/verify-direct.sh --ground-fallback` fingerprints proof inputs and tool binaries, translates offline, runs native differential checks, proves selected goals, audits generated-target classification, and compares inputs afterward. It must preserve the exact selected proof inputs and report the original-axiom subset used for any ground fallback. `scripts/verify.sh` runs the standard Why3find workflow with Z3/CVC5, fresh source spans, and no cache; it records native tests separately. When inputs change, preserve earlier bundles and mark them historical. Native checks, proof results, standard-library assumptions, and diagnostic-only solver runs are separate evidence classes.
