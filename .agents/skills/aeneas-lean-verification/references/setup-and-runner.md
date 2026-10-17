# Tool setup and local evidence

The shared Python helpers require Python 3.11 or newer (standard library only).
`charon`, `aeneas`, `lake` and their compatible toolchains must be on PATH via the
target environment. They are intentionally not installed or upgraded by the helpers.

## Layout and installation

Use the established version-local layout:

```text
<crate>/<version>/
  upstream/                 pinned unchanged Git submodule
  Cargo.toml, Cargo.lock    independent workspace; lib.path points into upstream
  scripts/                  env, setup, check-source, check-tools, fingerprint, verify
  proofs/                   lean-toolchain, lakefile.toml, lake-manifest.json
    <Generated>.lean       actual extraction
    Proofs/*.lean          authored proofs, no incomplete placeholders
  proofs.toml               proofs-rs public API mappings
  verification/             toolchain pins, specification, inventory, runs, results
```

Use `adler2/2.0.1/scripts/setup.sh` as a tested-component recipe, not a generic installer:
remove its crate path, ADLER_ROOT variable, API names and hardcoded tool pins when
adapting. Keep provenance checks crate-local. The shared source-capture utility is
`scripts/capture-crate-release.py`; inspect its CLI before use.

Resolve a compatible tuple from the selected proofs-rs registry/book and Aeneas's
`charon-pin`, Lean backend toolchain and Charon Rust toolchain. Record exact revisions,
URLs and feature/platform selection under the target. Build cargo-proofs with `--locked`.
Use a separate tool installation directory and version-local PATH so existing global
installations are not silently selected. Unset the native RUSTUP_TOOLCHAIN override
when building Charon with its own Rust toolchain. On the recorded macOS setup, Aeneas
uses OCaml/opam and GNU Make; Charon's documentation target required additional tools,
so its required Rust targets were built separately. Confirm current upstream targets
before reusing those commands.

The original adler2 tool tuple and minimal proofs-rs audit-variable patch are in its
`verification/toolchain.json` and `verification/patches/`. They are historical pins,
not a claim about today's latest versions. The patch avoids Aeneas's reserved `name`
token; its use must be checked against the newly chosen adapter version.

## Extraction configuration

Example `verification/aeneas.json` (replace all example names):

```json
{
  "entries": ["crate::State::new", "crate::State::update"],
  "llbc": "example.llbc",
  "cargo_args": ["--lib", "--locked"],
  "models": {
    "Example.lean": ["State.new", "State.update", "algorithm.compute"]
  }
}
```

Use definition names as they occur after `def` in generated Lean, not Rust paths.
Expected `.lean` filenames form an exact inventory, supporting multiple generated
files. Inspect output once to establish this configuration, then freeze it. Missing
bodies, unexpected files, extractor nonzero status, `axiom`, `opaque`, `partial def`,
`sorry` or `admit` fail extraction. The textual filter is conservative and not a Lean
parser; investigate a rejection rather than removing the axiom audit. Namespace/source
span review is still required. `crate::` avoids accidentally selecting a same-named
sysroot/registry crate, as happened with bare `adler2::` selectors.

## Theorem inventory

The auditor accepts the same inventory shape as adler2:

```json
{
  "checked": [
    {"name": "example.update_spec", "module": "Proofs.Update", "scope": "public-model"}
  ],
  "recorder_mappings": [
    {"api": "State::update", "theorem": "example.update_spec"}
  ],
  "extracted_but_unproved": []
}
```

Do not write this example as a claimed proof: create the actual theorem first.
`checked` must be nonempty and names unique. Each module is imported and audited
separately. With `--proofs-toml`, API/theorem mappings must match exactly, including
the module and `precondition`. A checked item's optional `precondition` defaults
to `"true"`; if a public contract needs a condition, document it explicitly in both
places and in the theorem. Metadata cannot prove the condition is adequate.
`extracted_but_unproved` is a manually reviewed coverage ledger; an empty list does
not automatically establish whole-crate correctness.

## Version-local verify runner

Use a fresh directory inside `verification/runs/` (ignored by Git). The runner should:

1. Check source and tool identity, actual Lake dependency revisions and clean sources.
2. Hash all Rust inputs, manifests/locks, generated and authored Lean, configuration,
   scope/specification, local/shared scripts, patches and tool binaries before work.
3. Invoke the shared extractor; compare every generated model with the maintained copy.
4. Run native tests for the selected feature sets, with separate logs and `--locked`.
5. Run `lake clean <local-package-name>` followed by the shared theorem auditor.
   A bare `lake clean` unnecessarily removes dependency builds. The auditor's `lake
   build` alone may reuse compiled targets; its result is only an audit, not a fresh
   complete verification run.
6. Repeat source/tool checks and the complete fingerprint, compare before/after, then
   write a success result with hashes of immutable logs and artifacts. Do not emit a
   success result on any failed step. Keep post-run results.md outside the fingerprint;
   never exclude proof-relevant inputs merely to make a run pass.

The auditor fingerprints proof source/configuration and its own code during execution,
but does not check source provenance, extraction correspondence, compiled dependency
freshness or native behavior. The surrounding runner supplies those checks. Output
must be outside the Lean source directory, to avoid hashing the audit's own outputs.

Use direct log redirection if Bash process substitution is blocked by the execution
sandbox. Keep commands visible in scripts and propagate errors (`set -euo pipefail`
for Bash). Never overwrite an accepted run to conceal changed inputs or a failed retry.

## proofs.rs recording

Local Lean verification and recording are separate. The adler2-tested cargo-proofs
0.4.0 commit did not initialize submodules in its temporary checkout, and required
committed/pushed inputs. Check the selected adapter's actual behavior before claiming
support. Submodule source links also need review. The shared helpers do not log in,
commit, push, record or publish. Follow the user's explicit authorization for external
actions; successful local audit does not mean `cargo proofs run` succeeded.
