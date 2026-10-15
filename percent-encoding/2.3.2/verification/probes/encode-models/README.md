# Encoder chunk-model feasibility probe

This probe imports the production `crate/src/encode_models.rs` by path. It
checks a logical model for the encoder's output request chunks, independently
of iterator/runtime implementation. The model consumes the four-word mask,
emits each escaped byte as one `%HH` chunk through the production
`crate::encoded_byte_model` shape (including space as `%20`), emits each
maximal unchanged ASCII run as one chunk, and recurses on the remaining input.
The isolated crate carries a small bridge definition for
`encoded_byte_model`; production integration resolves that reference to
`crate/src/lib.rs`.

`safe_run_end` is checked with in-bounds and four-word-mask preconditions. Its
postcondition gives bounds, safety for every byte before the endpoint, and
maximality (the endpoint is input end or a selected byte). `encoded_chunks`
has an empty-input case and a first-chunk/remaining-input recursion contract.
The caller must supply the selected mask, and this model alone does not prove
that the iterator's actual chunks equal this sequence.

Checked helpers `encoded_chunks_first_run` and
`encoded_chunks_first_escaped` expose the two first-step equations. The
`safe_run_end_unique` bridge accepts the concrete scan's in-bounds endpoint,
all-safe prefix, and stop condition, then proves equality with the model
endpoint.

Native `cargo check --offline` succeeds. Fresh Creusot-to-Coma translation
uses (the final freshness run is `diagnostics/fresh-05`):

```sh
cargo creusot --only=coma --span-mode off --output-dir diagnostics/fresh-01 -- --offline
```

The direct Why3/Z3 runner consumes the emitted Coma explicitly because this
probe's `cargo creusot` Why3find stage reports “No files to prove” despite the
Coma output:

```sh
python3 /workspace/proof-env/percent-encoding/2.3.2/scripts/diagnose-direct.py \
  --generated-dir diagnostics/fresh-05/verif \
  --target percent_encoding_encode_models_probe_rlib/encode_models/safe_run_end \
  --target percent_encoding_encode_models_probe_rlib/encode_models/safe_run_end_unique \
  --target percent_encoding_encode_models_probe_rlib/encode_models/encoded_chunks \
  --target percent_encoding_encode_models_probe_rlib/encode_models/encoded_chunks_first_run \
  --target percent_encoding_encode_models_probe_rlib/encode_models/encoded_chunks_first_escaped \
  --target percent_encoding_encode_models_probe_rlib/probe_safe_run \
  --target percent_encoding_encode_models_probe_rlib/probe_run_unique \
  --target percent_encoding_encode_models_probe_rlib/probe_first_run \
  --target percent_encoding_encode_models_probe_rlib/probe_first_escape \
  --output direct-checks-fresh-06
```

The latest saved diagnostic report is
`direct-checks-fresh-06/diagnostic-report.json`: nine positive roots, all nine
closed, including the scan uniqueness and both chunk first-step helpers. This
is a model-helper proof only. Iterator correspondence, formatter call order,
sink contents, and the public `Display` implementation remain to be proved by
integration.
