# Corrected heapless candidate: partial verification

The external-library assumption policy is recorded in [assumptions.md](assumptions.md).
The independent contract is [specification.md](specification.md). Neither document
assumes ipnet's own Display or Serialize implementation is correct.

This candidate fixes only IPNET-003's four feature cfg guards. The pinned published
2.12.2 source remains unchanged; this is not evidence that the original release
satisfies the heapless feature promise. Source identities and exact patch are in
`provenance.json` and `cfg.patch`.

## Achieved

- 22 Lean-checked conditional capacity theorems in `proofs/CapacityMath.lean` (fresh audit: `evidence/latest/capacity-axioms.log`):
  valid prefixes plus explicit external address/decimal text laws imply IPv4 <=18
  and IPv6 <=43 bytes. Abstract bounded writes and ordinary serializer Ok/Err
  propagation are separate helper results. These are not actual application-body
  proofs and are not added to the accepted 625-theorem API inventory.
- Fresh native evidence `evidence/latest/native-result.json`: all 10 combinations passed,
  6,216 cases per combination (62,160 checks). Features: heapless,
  heapless+serde, legacy ser_as_str+serde, both buffer features, and serde-only;
  each with candidate std enabled/disabled. All valid prefix lengths were exercised
  against 8 IPv4 and 10 IPv6 edge addresses, concrete/tagged variants, and both
  serializer success and error. Output equals actual Display; serializer query
  counts are checked. Buffer-feature cases allocated zero times during serialization
  with the nonallocating test serializer. Serde-only control allocated as expected.
- Candidate `cargo +1.91.1 test --offline --locked --manifest-path Cargo.toml
  --features heapless`: 37 unit tests and 56 doctests passed; includes existing
  binary serde tests. Log: `evidence/latest/candidate-tests.log`.
- Candidate `cargo +1.91.1 check --offline --locked --manifest-path Cargo.toml
  --no-default-features --features ser_as_str` passed (legacy without serde is
  compilation-only, not a Serialize test).
- The candidate source/provenance check preserves the unchanged accepted
  baseline inputs; the current baseline is rerun separately by `scripts/verify.sh`.

Native checks are finite and use a std-based test executable, even when the
candidate's std feature is disabled. They do not prove a freestanding no_std target,
all addresses, or arbitrary external serializer behavior. Rerun the matrix with
`python3 native/check.py` from this directory or its absolute path elsewhere.

## Unresolved actual-body proof

Actual IPv4/IPv6 Serialize extraction stops at the mutable trait-object cast
`&mut heapless::String<N> -> &mut dyn core::fmt::Write`. Optimized MIR and including
external fmt::write do not remove this obstacle. The missing representation of
buffer updates cannot soundly be replaced by a shared-reference or identity cast.
Tagged IpNet serialization depends on these concrete bodies. Logs and hashes are
recorded in `evidence/latest/result.json`. Historical optimized-MIR and
formatter-include probes remain local in ignored `runs/` and are not claimed
as fresh committed execution evidence.

Actual Display extracts separately, but the existing external Formatter model does
not retain emitted text. A callback-aware, state-preserving formatting bridge is
still required. CapacityMath's abstract three-write renderer is not proved equal to
actual formatting, which may fragment writes. Its pure, terminating serializer
function does not model mutable state, panic or divergence. Its zero-allocation
result assumes abstract write effects and is not a Rust allocation proof.

Astra reviewed the independent specification and these limitations; Sol supplied
Lean helpers and extraction investigations. Full corrected heapless verification
remains blocked on this application-to-external-formatting connection, even with
external-library laws explicitly permitted. No new distinct ipnet bug was found.
