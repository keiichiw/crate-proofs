# Isolated UTF-8 standard-library probe

This package imports `crate/src/stdlib_models.rs` by path and calls
`String::from_utf8_lossy`; it does not change the release crate's module graph.
From this directory, translate it with:

```sh
source /workspace/proof-env/scripts/activate.sh
cargo creusot --only=coma --span-mode off --output-dir /tmp/form-url-stdlib-probe-coma -- --locked --offline
```

On 2026-10-13 this command completed and generated
`form_urlencoded_stdlib_probe_rlib/lossy.coma`. The generated Coma contains
the recursive UTF-8 model definitions and the `Cow::Borrowed` / `Cow::Owned`
postcondition. This is a translation check only; it has not run a Why3 proof and
does not substitute for the parent crate's fresh proof bundle.
