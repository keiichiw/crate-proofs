# Strict UTF-8 standard-library boundary probe

This isolated crate models `str::from_utf8`, `String::from_utf8`, and
`FromUtf8Error::utf8_error` as explicit standard-library boundaries, then
checks a `Cow<[u8]> -> Result<Cow<str>, Utf8Error>` wrapper. The UTF-8 predicate
is existential: a byte sequence is valid exactly when it equals the UTF-8
encoding of some `Seq<char>`. Success contracts preserve exact scalar content
and the wrapper preserves borrowed/owned input policy; an error result implies
the input bytes are invalid.

The external contracts are assumptions about Rust's standard library, not
proofs of its implementation. `Utf8Error::valid_up_to` and `error_len` are not
modeled, so the probe does not claim exact error offsets or equality of error
details across the borrowed and owned standard-library paths. The
`utf8_error` accessor is given only a vacuous postcondition because the wrapper
does not inspect its fields. No duplicate lossy-conversion extern spec is
declared here.

The final clean Coma translation and direct Z3 checks are recorded in
`diagnostics/run-07/`. All 10 roots and all 22 exported SMT goals closed; the
12 goals for `strict_cow_decode` were `unsat` with a 5-second per-goal
standalone Z3 timeout. This establishes that the wrapper contract follows
from the declared standard-library contracts; it does not validate those
contracts against the Rust implementation.

An intermediate incremental attempt in `run-06` did not emit new Coma files
because Cargo reused its cached target. The final run cleaned the probe target
before translation; its output is the fresh evidence cited above.

Reproduce from this directory after sourcing the offline environment:

```sh
source /workspace/proof-env/scripts/activate.sh
cargo creusot --only=coma --span-mode off --output-dir diagnostics/run-07/coma -- --locked --offline
PROBE_Z3_TIMEOUT=5 python3 scripts/check_roots.py diagnostics/run-07/coma/verif/percent_encoding_strict_utf8_boundary_probe_rlib/strict_cow_decode.coma diagnostics/run-07/direct-root-checks
```
