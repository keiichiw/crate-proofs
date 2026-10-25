# bytes 1.12.1 — Take contracts and signed-read findings

This report verifies five structural `Take` contracts using Aeneas and Lean:
`into_inner`, `get_ref`, `get_mut`, `limit`, and `set_limit`. The unchanged release
source is restored from the checksummed archive; generated Lean is never edited.

- [Report and Finding](aeneas/profiles/unpatched/proofs.toml), with three related
  signed-reader API paths.
- [Specification](aeneas/profiles/unpatched/specification.md),
  [theorem inventory](aeneas/profiles/unpatched/theorems.json), and
  [results](aeneas/profiles/unpatched/results.md).
- [Signed-read Finding and provenance](verification/findings/BYTES-001.md).

The Finding arose while working toward formal verification: the desired signed
contract was not established, and source review and native reproduction confirmed
zero extension for short negative inputs. Proof failure alone is not evidence of
a bug. Native counterexamples are separate from the five successful contracts.
Upstream PR #839 fixed the readers on master; as checked on 2026-10-25, the latest
release is still affected 1.12.1.

## Reproduce

The default `unpatched` profile pins Aeneas, Charon and Lean in
`aeneas/profiles/unpatched/toolchain.lock.json`.

From this version directory:

```sh
bash scripts/setup.sh
bash scripts/verify.sh
```

Use `--offline` when source/tool/dependency caches are already prepared. The runner
checks source and tool identities, runs native tests and the Finding reproduction,
regenerates the selected model and compares it byte-for-byte, builds Lean, audits
all five theorems and compares before/after input fingerprints. Native outcomes and
formal contracts remain separate. The accepted platform is recorded in results;
other platforms are not claimed by this profile.

The recording CLI retains its historical preparation/provenance patch. That patch
does not modify Aeneas, Charon, Lean or the generated model. This profile adds no
compiler/model patches, and does not inherit the patched profile's proof coverage.
For Finding `api_paths` authoring, use the current proofs-rs CLI; the historical
recorder is not a substitute for that authoring feature.

## Historical patched profile

`aeneas/profiles/default/` preserves the earlier nine-model, 56-mapping proof with
its core/numeric/stage3 compiler patches and ordinary negative control. It is not
the default profile or evidence for the new five-contract report. Explicit replay
uses `--profile default` and selects the historical patched tools. Select
`--profile unpatched` again before further current-profile work.

The old preview records and local-only SARIF under `verification/preview/2026-10-23`
belong to that historical experiment. Do not use them to present current coverage.
See [reorganization provenance](verification/reorganization.md). No verification
command uploads or publishes evidence.
