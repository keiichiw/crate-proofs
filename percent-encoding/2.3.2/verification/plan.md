# Verification plan

## Identity and workspace

The target is the captured `percent-encoding` 2.3.2 release. The immutable eight-file capture is under `capture/`; the independent verification fork is under `crate/`. The capture checksum is `9b4f627cb1b25917193a259e49bdad08f671f8d9708acfd5fe0a8c1455d87220`. The offline registry index provenance is recorded under `verification/provenance/`; it is a normalized local cache entry, not a live registry response. These establish the captured archive identity against its stored checksum, not identity between the verification fork and an upstream source-control commit.

The verification crate aliases the already checked local `form_urlencoded 1.2.2` fork by path. That dependency retains its registry `percent-encoding` dependency, so no global override or cycle is introduced. Enabling `alloc` on the local dependency changes this verification workspace's dependency footprint; the upstream Rust 1.51 MSRV is not claimed for the fork.

## Current proof scope

The current goal is checked coverage of the feasible public API and its generated proof obligations, not only the initial byte-core milestone. The selected scope includes:

- Per-byte unconditional uppercase `%HH` encoding, including `%20` for space, the local numeric helper, and constructors that preserve input bytes and the configured four-word `AsciiSet` mask.
- `AsciiSet` exact constants, private-mask logical view, ASCII membership and encoding decision, ASCII-domain `add`/`remove`, union/complement, `Add`/`Not`, equality, and Debug request trace.
- Percent decoder construction, checked ASCII hexadecimal parsing, percent lookahead, exact malformed-input consumption, the local recursive decoded trace, iterator refinement/laws, and size hints.
- Percent encoder chunk model, iterator refinement/laws, size hints, state cloning/equality, and `Into<Cow<str>>` byte content plus borrowed/owned boundary by chunk count.
- Decoder `Cow<[u8]>`, strict UTF-8 and lossy UTF-8 conversion contracts, including strict error offsets/lengths and inherited standard-library lossy policy where applicable.
- Display's ordered formatter requests and first-error propagation, and Debug's requested structure, field names/order, typed values, and returned status.

The concrete selected targets and all generated target classifications belong in `target-inventory.json`; run-specific proof results belong in `results.md` and the immutable evidence bundle. Every selected generated body, refinement, helper, and law must have a positive root and closed proof obligations. Targets for APIs with no emitted Creusot goal must be identified as such rather than assigned invented proof counts. Genuine standard-library model boundaries are recorded in `assumptions.md` and the dependency ledger.

The local models are connected to checked `form_urlencoded` models through public contracts and checked bridge lemmas. Opaque dependency models without an exported base case or full recurrence are not treated as a global theorem. The local decoder recurrence supplies its own empty-input base. UTF-8 and formatter behavior are proved only to the exact exported standard-library contracts; formatter proofs concern requested calls, values, ordering, and error propagation, not bytes rendered by an arbitrary sink.

## Historical milestone

The earlier 21-target byte-core bundle is retained as historical evidence under `verification/evidence/percent-encoding-v49MYwzO/`. It is not the current scope or a substitute for a fresh run over the expanded API. The initial 21-target inventory and its previous status are preserved in that bundle.

## Final run requirements

After source and documentation freeze, regenerate Coma in a unique directory, fingerprint the exact source/dependency inputs, enumerate every emitted target, and run the independent proof runner on the manifest-selected set. Require successful translation, positive roots, all selected goal trees closed, no unclassified emitted targets, and fresh native/differential checks. Keep primary Z3 results and any explicitly approved secondary CVC5 results separate, with exact SMT hashes, commands, versions, and time limits. Translation alone and finite differential tests are not proof results.
