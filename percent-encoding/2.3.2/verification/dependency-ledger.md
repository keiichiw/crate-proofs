# Verified dependency chain

This pin identifies the newly audited macOS arm64 dependency bundle. It is immutable; the moving `latest-direct` link is not used as its identity. Earlier Linux evidence remains historical. Changes to dependency proof inputs require another fresh dependency run and an explicit pin update before a dependent proof.

The verification fork uses `form-model`, a Cargo alias for the local
`form_urlencoded 1.2.2` verification fork. Its source identity is fixed by the file hashes below and the dependency evidence manifest. Its own `percent-encoding 2.3.2` dependency remains a registry
package. The new local percent-encoding package is not globally patched into
that dependency, so the Cargo and logical dependency graphs are acyclic.

The reusable evidence is
`../../../form_urlencoded/1.2.2/verification/evidence/form-urlencoded-etJOlOat/manifest.json`.
The manifest SHA-256 is
`7e9efe7807c704fe2bdbc18da585051dcf479c112dc6ffe682f771168ae2a153`.
The dependency's `crate/src/lib.rs` SHA-256 is
`8e4d6fd4011272b2bc4ef01281f859f270edd0814a1e21c3a5c7cd89406e92fd`.
The dependency's `crate/Cargo.toml` SHA-256 is
`9f09b794f81c87031b19a40f4399f7ac7fee35920d324ad1372ba64c30bff77e`.

A fresh standard Why3find proof with Z3/CVC5 and a read-only root-reconstructing archive audit on 2026-10-17 UTC passed. Exact goal and input counts are recorded in the dependency manifest and its `audit.log`. This is the selected first-order scope of form_urlencoded, not its entire
public API. Its standard-library assumptions and upstream correspondence limits
remain part of the dependency chain.

## Required logical use

The encoder can consume the checked `encoded_array_model` result for bytes
other than space. `uppercase_hex` and `ascii_three` supply the corresponding
numeric specification. Space needs a separate checked `%20` bridge:
form_urlencoded's `escaped_byte_chunk(32)` is `+` and is unsuitable for an
unconditional generic percent encoder.

The raw percent-decoding model preserves `+`; form's plus-to-space conversion
is a separate operation. The checked `percent_decoded_from_step` lemma is
available for nonempty input. The dependency does not export every base-case
or suffix-normalization lemma needed to unfold its opaque decoder model across
crate boundaries. Additional local checked definitions or bridges must be
reported as new proof work, not inherited guarantees.

Each passing new evidence bundle must pin the dependency source and manifest,
audit the pinned dependency evidence against its current inputs, classify all new generated targets, and inspect actual
uses of dependency contracts in generated proof obligations. An unused import
or a prose citation alone does not establish proof reuse. No new proof result
is asserted by this ledger; the final result report and audited manifest provide
the completed scope.
