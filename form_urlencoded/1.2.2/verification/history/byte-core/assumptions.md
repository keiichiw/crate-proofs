# Model and exclusion ledger

No application-level `trusted` declarations or custom axioms are used. Selected target contracts are checked against their Rust bodies.

Creusot 0.13 and `creusot-std` 0.13 models are part of the verifier boundary. In particular, selected code uses the `u8` model, integer arithmetic, slice indexing/length, and mutable-slice model. Their exact versions and source/tool hashes are recorded by the fresh run manifest.

`percent-encoding` 2.3.2 is used only by the excluded percent-decoder path in this milestone. The selected exact percent-byte encoding is implemented locally by a checked exhaustive 256-arm match over static numeric-byte triples. No percent-encoding algorithm is trusted. Why3's configured five-second prover budget is a search resource, not an added assumption.

`String::from_utf8_lossy`, `percent_decode`, `Cow` ownership and allocation behavior, custom `IteratorSpec` refinement, `EncodingOverride`, `Target`, and public `Serializer` methods are excluded. The three custom `Iterator` impls and serializer API are compiled only with `cfg(not(creusot))` because Creusot 0.13 cannot translate their trait-object / IteratorSpec surface as currently modeled. Native builds retain them. The evidence does not establish their formal behavior.
