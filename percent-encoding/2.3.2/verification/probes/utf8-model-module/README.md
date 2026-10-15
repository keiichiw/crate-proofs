# Production UTF-8 model module probe

This probe is now evidence for `crate/src/utf8_models.rs` in the integrated
crate. It provides strict existential validity, `Cow` strict decoding, and
the lossy relation/owned-buffer helper. The local `utf8_step` and recursive
`strict_error` definitions model the first invalid offset and error length;
`error_len = None` is selected only for an incomplete valid multibyte prefix
at end of input. A copied, `repr(Seq<Int>)`-based step parser is used so the
old form crate model remains unchanged.

The initial private-module feasibility probe (`diagnostics/run-05`) closed its
strict wrapper with 2 roots / 2 SMT goals and lossy wrapper with 3 roots / 3
SMT goals. The newer clean Coma translation is
`diagnostics/error-model-attempt-13/coma`. Its direct checks close the
`utf8_step_bounds` root (2 SMT goals), 12 individual `strict_error_*` vector
roots (12 SMT goals), and the strict helper (8 roots / 19 SMT goals). Vectors
cover invalid lead bytes, valid prefixes, 2/3/4-byte truncation, bad third and
fourth bytes, surrogate/overlong/out-of-range input, and valid ASCII/multibyte
input. These are concrete checks of the recursive model, not a universal
equivalence theorem to the Rust parser.

One direct check remains open: the public PercentDecode strict-wrapper
postcondition has 4 roots / 5 SMT goals, with the final decoded-trace relation
goal timing out at 5 seconds (`direct-checks/strict-public-wrapper/`). The
strict helper itself closes all goals. This wrapper timeout is not a success
claim and needs a checked bridge or a documented open target before final
proof coverage is stated.

At the standard-library boundary, opaque observers model
`Utf8Error::valid_up_to` and `error_len`. The `str::from_utf8` extern contract
assumes successful content/validity and Err classification agree with the
existential character model, and assumes its error observers agree with the
local recursive parser. The local parser's recursive bounds and concrete
edge cases are checked; adequacy of the standard-library implementation and
equivalence between parser validity and the separate existential character
model remain assumptions. No application algorithm is trusted. Lossy
content/Cow policy uses the inherited standard-library model; it is not
bridged to this separate strict parser.

The lossy helper replaces the old debug-only pointer-identity assertion with
a debug-only byte-content assertion. This adds a linear content comparison in
debug builds; `debug_assert_eq!` is compiled out in release builds. It makes no
pointer provenance claim and introduces no release-path allocation or other
runtime change. Native upstream differential evidence is recorded separately
under `verification/differential/` for the earlier byte-core version.

The full-scope native differential harness compares `valid_up_to` and
`error_len` for every strict-UTF8 error it encounters, plus forced owned
invalid inputs. The recorded passing attempt followed the scan fix but predates
the final error-model and Debug sink additions, so it is historical evidence.

The attempt directories are diagnostic milestones while core integration is
still active; `attempt-13` is not a final source-freeze snapshot. A final
translation and proof must capture matching pre/post source fingerprints.

Reproduce the integrated checks from the version directory after core declares
the source stable:

```sh
source /workspace/proof-env/scripts/activate.sh
bash verification/probes/utf8-model-module/scripts/run-error-model-checks.sh error-model-final
```

The runner stores fresh Coma, tool versions, direct checker summaries, and
matching source/dependency fingerprints under the chosen diagnostics folder.
Its output names the one remaining public-wrapper timeout until core resolves
that obligation; a successful script exit requires every selected target to
close.
