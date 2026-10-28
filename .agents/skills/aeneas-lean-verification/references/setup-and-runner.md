# Tool setup and local evidence

The shared Python helpers require Python 3.11 or newer (standard library only).
`charon`, `aeneas`, `lake` and their compatible toolchains must be on PATH via the
target environment. They are intentionally not installed or upgraded by the helpers.

## Managed layout and installation

For new targets and explicit migrations, use the common runner described in
[the management guide](../../../../verification/aeneas-management.md). Each version
has source.lock.json, an independent Cargo workspace, thin setup/verify wrappers,
and aeneas/profiles/<name> with tool locks, patches, specifications, proofs and
evidence. Source and build products stay ignored. Migrated Aeneas workspaces use the managed
layout; their accepted runs describe original inputs, not proof freshness of subsequent edits. Start with the [new-crate procedure](../../../../verification/templates/aeneas-managed/README.md).

The common setup preserves caller tool homes and checks pinned sources, patch
application and host builds. Its execution logs stay local; the recorder checks
provenance and performs standard Lean verification independently. Never replace
this boundary with a script-provided success marker.

## Historical layouts

Earlier work used submodules, version-local tool installations and custom runners.
Follow an unmigrated target's own instructions when reproducing its existing work.
Use the managed new-crate procedure for new work. Full old setup recipes are in local archives identified by each
profile's evidence/archive.json, not necessarily distributed under evidence/legacy.
Reader-facing historical documentation is retired; only explicitly inventoried
compatibility fixtures remain distributed. Never copy historical absolute paths,
crate identities, success claims or tool patches into a new workspace.

## Extraction configuration

Example profile `extraction.json` (replace all example names):

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
Ordinary `entries` may be empty when validated `impl_entries` or
`foreign_impl_entries` supply at least one root; an empty combined selection is
rejected. This avoids introducing unrelated generic dictionaries for impl-only
verification.

Expected `.lean` filenames form an exact inventory, supporting multiple generated
files. Inspect output once to establish this configuration, then freeze it. Missing
bodies, unexpected files, extractor nonzero status, `axiom`, `opaque`, `partial def`,
`sorry` or `admit` fail extraction. The textual filter is conservative and not a Lean
parser; investigate a rejection rather than removing the axiom audit. Namespace/source
span review is still required. `crate::` avoids accidentally selecting a same-named
sysroot/registry crate, as happened with bare `adler2::` selectors.

For crates whose unrelated declarations cannot be translated, `local_scope` may
limit traversal while retaining the original selected bodies:

```json
"local_scope": {
  "opaque_crate": true,
  "include": ["crate::buf::take::Take", "crate::buf::take::new",
              "crate::buf::take::_::limit"]
}
```

This passes `--opaque crate` followed by explicit `--include` selectors. Local includes
also accept the same validated local trait-impl method syntax as `impl_entries`,
for example `{impl crate::Integer for _}::div_floor`; arbitrary wildcard paths
remain rejected. A single
intermediate `_` matches Charon's inherent impl component; arbitrary wildcards
and a terminal `_` are rejected. Select the needed types and dependency bodies
as well as entry functions. The generated-file inventory, required-body checks,
and prohibition on generated axioms still apply. This option cannot be combined
with `extract_opaque_bodies`, and does not establish coverage of omitted methods.

`dependency_include` selects explicit dependency source paths or trait-impl
methods such as `{impl num_traits::identities::Zero for _}::is_zero`. These are
transparent original bodies, not trusted replacements. Arbitrary wildcard paths
are rejected, and the same complete-output/body/axiom checks apply.

The optional boolean `remove_unused_clauses` (default `false`) passes Charon's
`--remove-unused-clauses` flag. This can remove unused trait bounds from field-only
wrappers; it does not assume the corresponding trait's behavioral or safety laws.
Generated body and axiom checks remain mandatory.

`charon_exclude` optionally lists exact `crate::`, `core::`, `alloc::`, or `std::`
paths without wildcard components. Every selected generated body must still be
present, complete and free of application axioms. Excluding an unused trait
declaration does not establish its operational laws.

The optional boolean `rooted_declarations` (default `false`) selects the locally
reviewed Aeneas `-rooted-declarations -filter-trait-methods` options. It requires a
tool build that implements the recorded dependency-closure pass; standard builds
need not support it. Record the tool patch and regressions. This limits emitted
declarations to explicit function roots and retained dependencies; it never
licenses dropping a reachable unsupported operation or changing its result.

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

## Runner responsibilities (reference)

Use the common managed runner, which creates a fresh `.work/runs/` directory.
Do not implement a replacement runner for a new crate. Its responsibilities are:

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

## proofs.rs recording (historical compatibility context)

Local Lean verification and recording are separate. The adler2-tested cargo-proofs
0.4.0 commit did not initialize submodules in its temporary checkout, and required
committed/pushed inputs. Check the selected adapter's actual behavior before claiming
support. Submodule source links also need review. The shared helpers do not log in,
commit, push, record or publish. Follow the user's explicit authorization for external
actions; successful local audit does not mean `cargo proofs run` succeeded.
