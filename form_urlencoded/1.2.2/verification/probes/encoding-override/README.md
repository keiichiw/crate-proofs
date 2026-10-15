# Exact `EncodingOverride` translation probe

This probe preserves the public callback shape from `crate/src/lib.rs`: an
optional borrowed `dyn Fn(&str) -> Cow<[u8]>`, stored by a setter, and invoked
through the trait object. It is isolated so the translation result cannot be
mistaken for a Serializer body proof.

Run from this directory with the repository tool environment:

```sh
source /workspace/proof-env/scripts/activate.sh
cargo creusot --only=coma --span-mode off --output-dir /tmp/form-urlencoded-encoding-override-coma -- --locked --offline
```

Translation fails at the dynamic `Fn` call with `forbidden dyn type`; see
`../../diagnostics/encoding-override-probe.log`. The result records a current
Creusot 0.13 limitation. It does not provide any callback behavior assumption.
