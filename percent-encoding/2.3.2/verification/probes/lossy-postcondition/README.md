# `String::from_utf8_lossy` postcondition probe

This isolated crate checks whether a contract can refer to the inherited `String::from_utf8_lossy` standard-library postcondition and the checked `form_urlencoded::cow_str_scalars` observer. The probe does not import the form crate's private `stdlib_models` module, declare duplicate extern specs, edit production sources, or establish a production proof.

The workspace depends on the checked form fork through the local `form-model` alias. Translation from this directory:

```sh
source /workspace/proof-env/scripts/activate.sh
cargo creusot --only=coma --span-mode off --output-dir /workspace/proof-env/percent-encoding/2.3.2/verification/probes/lossy-postcondition/diagnostics/run-02/coma -- --locked --offline
```

The first attempt used `#[logic(open)]` for `lossy_relation` and failed because `FnExt::postcondition` is prophetic. Marking the relation `#[logic(open, prophetic)]` fixed the translation without changing the model or introducing an assumption. The initial failure is in `diagnostics/run-01/translation.log`; the successful fresh Coma translation is in `diagnostics/run-02/translation.log`.

Why3 listed two roots in the generated Coma: `vc_from_utf8_lossy` is the trivial `true` root from the inherited external model, and `vc_std_lossy_probe` is the wrapper-preservation obligation. The second root was exported with `compute_specified` and `split_vc`; direct Z3 4.15.3 returned `unsat`. The generated task and command output are in `diagnostics/run-02/direct-exports/vc_std_lossy_probe/`. The root listing and tool versions are in `diagnostics/run-02/roots.log` and `versions.txt`. A separate `why3 prove -P Z3` attempt is recorded in `diagnostics/run-02/why3-z3-roots.log`; this environment blocks Why3's `why3server` socket (`Operation not permitted`), so the checked solver result is from standalone Z3 on the exported SMT-LIB file.

Reproduce the root listing and the direct SMT check from this directory after sourcing the environment:

```sh
WHY3_CONF="$XDG_DATA_HOME/creusot/creusot_why3.conf"
CREUSOT_LIB="$XDG_DATA_HOME/creusot/share/why3find/packages/creusot"
COMA=diagnostics/run-02/coma/verif/percent_encoding_lossy_postcondition_probe_rlib/std_lossy_probe.coma
why3 prove -C "$WHY3_CONF" -L "$CREUSOT_LIB" "$COMA"
why3 prove -C "$WHY3_CONF" -L "$CREUSOT_LIB" "$COMA" -T Coma -G vc_std_lossy_probe -a compute_specified -a split_vc -P Z3 -o diagnostics/run-02/direct-exports/vc_std_lossy_probe
z3 -smt2 -T:30 sat.random_seed=42 nlsat.randomize=false smt.random_seed=42 diagnostics/run-02/direct-exports/vc_std_lossy_probe/std_lossy_probe-Coma-vc_std_lossy_probe.smt2
```

The result is conditional on Creusot's inherited `String::from_utf8_lossy` model, which supplies the lossy-output and Cow-variant postcondition. This probe checks that a wrapper contract can preserve that imported contract through a prophetic logical relation. It does not verify the Rust standard-library implementation, prove the model itself, or prove any percent-encoding production API.

## Owned `Cow<[u8]>` extension

The isolated `cow_lossy_decode` wrapper reproduces the form crate's borrowed and owned branches, including its UTF-8 borrowed-to-owned conversion. Its contract relates the original byte trace to the scalar trace through an existential witness for the public standard-library postcondition. The owned branch binds the concrete `from_utf8_lossy` result and asserts its inherited postcondition and relation before matching the Cow variant; this exposes the witness needed by the solver without adding assumptions or duplicate extern specifications.

Fresh Coma translation for this extension is in `diagnostics/run-06/translation.log`, with generated roots under `diagnostics/run-06/coma/`. Direct standalone Z3 checking of all 10 roots and all 20 exported SMT goals passed (`unsat`) with a 5-second per-goal timeout; see `diagnostics/run-06/direct-root-checks/summary.json` and `check.log`. The checker uses transformed exports for the function root and untransformed exports for the inherited helper roots. Earlier bounded attempt `run-05` had 7 of 9 function leaves close and timed out on two existential leaves; the explicit witness assertions close both in `run-06`. This is a feasibility probe against the inherited standard-library model, not a production-crate proof or a claim about the standard-library implementation.
