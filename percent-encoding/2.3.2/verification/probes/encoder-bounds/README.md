# Encoder chunk-count bounds probe

This probe imports the production `crate/src/encode_models.rs` and
`crate/src/encoder_bounds.rs` by path. It checks the all-input count theorem
needed to connect the encoder's `Iterator::size_hint` upper/lower bounds to
the encoded chunk model. The helper requires a four-word mask and establishes:

- `encoded_chunks(mask, input).len() <= input.len()`;
- empty input iff the encoded chunk sequence is empty;
- nonempty input has at least one encoded chunk.

The recursive proof follows the existing chunk recurrence: an escaped byte
recurses on the one-byte-shorter suffix, while an unchanged run recurses at
`safe_run_end`, which advances at least one byte. It composes the existing
checked `encoded_chunks_first_escaped` and `encoded_chunks_first_run` lemmas;
it does not change or duplicate `encode_models.rs`.

Run the native check and fresh translation from this directory:

```sh
cargo check --offline --locked
cargo creusot --only=coma --span-mode off --output-dir diagnostics/run-02/coma -- --locked --offline
```

The direct checker consumes the emitted goals explicitly:

```sh
python3 /workspace/proof-env/percent-encoding/2.3.2/scripts/diagnose-direct.py \
  --generated-dir diagnostics/run-02/coma/verif \
  --target percent_encoding_encoder_bounds_probe_rlib/encode_models/safe_run_end \
  --target percent_encoding_encoder_bounds_probe_rlib/encode_models/safe_run_end_unique \
  --target percent_encoding_encoder_bounds_probe_rlib/encode_models/encoded_chunks \
  --target percent_encoding_encoder_bounds_probe_rlib/encode_models/encoded_chunks_first_run \
  --target percent_encoding_encoder_bounds_probe_rlib/encode_models/encoded_chunks_first_escaped \
  --target percent_encoding_encoder_bounds_probe_rlib/encoder_bounds/encoded_chunk_count_bounds \
  --target percent_encoding_encoder_bounds_probe_rlib/probe_encoded_chunk_count_bounds \
  --output diagnostics/run-02/direct
```

The fresh direct report is `diagnostics/run-02/direct/diagnostic-report.json`:
all seven selected targets have positive roots, and all seven close. This is
evidence for the chunk-model bounds only; it does not prove the public iterator
or its `size_hint` refinement. The core module must call this checked helper
from its public size-hint contract and re-run the integrated selected audit.

Inputs were fingerprinted before the final translation and rechecked
afterward. The hashes of `encoder_bounds.rs`, `encode_models.rs`, this probe's
`src/lib.rs`, `Cargo.toml`, and `Cargo.lock` were unchanged across that run.
