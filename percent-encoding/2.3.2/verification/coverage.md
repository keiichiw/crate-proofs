# Verification scope

The selected scope covers byte encoding/decoding, exact `AsciiSet` models and operations, both iterator traces and size hints, clone/equality, Cow conversions, strict/lossy UTF-8 wrappers, and checked Display/Debug call traces. Precise contracts and domains are in [specification.md](specification.md) and [public-api-inventory.md](public-api-inventory.md).

Run outcomes, native-test counts, the selected evidence bundle, and current-input freshness are maintained in [results.md](results.md). The archived integrated run completed the selected proof obligations; earlier targeted diagnostics and byte-core runs do not replace it. Changes to fingerprinted inputs require a fresh run.

[target-inventory.json](target-inventory.json) defines the selected generated targets and the excluded compile-time `ascii_set/static_assert` target. Every fresh run must regenerate all Coma, classify every emitted target, and close every selected root, including helpers, refinements, and laws. The local form_urlencoded dependency must have freshly audited matching evidence before this dependent run; its reviewed pin is documented in [dependency-ledger.md](dependency-ledger.md).

Native unit, documentation, feature-matrix, and differential checks are separate evidence. They establish tested runtime behavior, not all-input equivalence. Standard-library boundaries and formatter request-trace limits are stated in [assumptions.md](assumptions.md). Rendered text, arbitrary sink effects, allocation/OOM, out-of-domain ASCII indexing, individual inherited library methods, upstream MSRV, and all-platform behavior are not guaranteed.

For standard Why3find reproduction, regenerate native logs with `verification/differential/run-full-scope.sh`, then run `scripts/verify-why3find.sh`. The successful standard bundle is selected by `evidence/latest-why3find`; the direct-SMT `evidence/latest` pointer is historical for its frozen inputs.
