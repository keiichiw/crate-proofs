# Writing proofs.toml

Read the official [writing guide](https://proofs.rs/book/write-a-report) and
`write-proofs-report` skill first, as described in the entrypoint. They supply the
editorial approach; this reference adds repository-specific checks. Keep conditions
beside the guarantee and explain why material trust and adaptations are acceptable.
Leave routine commands, hashes and development history in evidence artifacts.

## Markdown

`title` is plain text. `explanation`, `trusted_assumptions`, `limitations` and
`environment` render Markdown, as does each finding's `body`. Use headings,
paragraphs, emphasis, lists, links, blockquotes, fenced/inline code, tables and
strikethrough where useful. Begin headings at `#`: the renderer nests them inside
the page's preset sections. Raw HTML is displayed as text, images are disabled,
and code fences have no syntax highlighting. Check the pinned renderer if behavior
differs. See [Configuration and Markdown](https://proofs.rs/book/configuration#markdown-in-reports).

Prefer TOML multiline literal strings (`'''`) for Markdown and backslashes.
If content contains that delimiter, choose valid TOML that preserves the text and
parse the result. Review the rendered output, not just the TOML source.

## Reader-facing fields

Preserve the existing file and edit fields in place. The common shape is:

```toml
[report]
title = "Selected parsing contracts for example 1.2.3"
explanation = '''
Describe the behavior established by the selected contracts.
'''
trusted_assumptions = '''
Describe the external models and translation/prover trust boundary.
'''
limitations = '''
Describe unproved APIs, input domains and behavior outside the model.
'''
environment = '''
Identify the supporting run, source/tool pins, target and features.
'''
```

This is a prose scaffold, not a complete runnable configuration. Replace example
text with supported facts; retain `[tool]` and other existing configuration. An
editorial-only file without tool/claim configuration must remain labeled a draft.

| Field | What belongs here |
| --- | --- |
| `title` | Crate/version and the concrete selected behavior; make partial scope clear. |
| `explanation` | Observable results, errors, consumed input, post-state and ownership/iterator guarantees actually established. Explain decisive premises and give a small example when helpful. |
| `trusted_assumptions` | Unproved standard/external models, axioms, translation and solver/kernel dependencies. Distinguish checked bridges from assumed relations. |
| `limitations` | Excluded APIs, concrete implementations/types, features and targets; safety, allocation, panic or formatting behavior outside the model when relevant. |
| `environment` | Concise reproduction configuration, material patches and evidence references; target/features and overflow settings when needed to interpret the result. Avoid duplicating metadata already supplied by the recorded run. |

Lead with behavior readers can assess. Avoid file-by-file work histories, generic
claims such as “fully verified,” and theorem counts without their API scope.
Say whether a theorem ensures successful execution, only constrains a successful
result, or proves a conditional law. A single-step iterator result does not imply
whole-iterator laws; an abstract model theorem needs its implementation bridge.
Put a new observation in findings only when it adds information beyond these fields.

## Tool and mapping fields

Use the target's pinned CLI as the authority. In the inspected CLI format:

- Crate/version come from Cargo metadata; there is no `[crate]` table. `[tool]`
  identifies one verifier and its actual version. Do not invent registration status.
- Creusot requires `target = "annotated"` or `"all"`. This is source discovery,
  not proof completion; CLI `--target` selects a Rust compilation target instead.
- Kani uses discovered contract harnesses; `[tool].target` is not accepted. Report
  harness restrictions, stubs and concrete types beyond extracted `requires`.
- Explicit Aeneas `[[tool.proofs]]` entries contain `api`, `module`, `theorem` and
  applicable `precondition`. Verify each against the actual theorem and inventory.
  Helper/model/loop lemmas do not become API claims just because they build.
- Newer Aeneas adapters also support `proof_modules` and `translation_manifest`;
  use these only when the target's pinned adapter and translation artifacts support
  them. Do not replace a managed target's explicit registry during a prose edit.
- `lean_dir` is relative to the selected Cargo package. Keep managed profile paths
  intact; do not relocate them to match a generic example.
- Preserve `[dependencies]` reviews unless asked to change them. Omission preserves
  reviews on update; an explicitly empty table clears them. Reviews pin report and
  revision, and do not certify all dependencies or a path/Git fork with the same name.

For Aeneas audit comparison, inspect `scripts/aeneas-audit.py`: the ordered API and
theorem mappings must equal `recorder_mappings`, and module/precondition must match
the corresponding checked inventory item. Metadata agreement alone does not rerun
the named-theorem and transitive-axiom audit or establish Rust/model correspondence.

## Local preview

From the selected package, when its CLI supports draft mode:

```sh
cargo proofs preview --draft --no-browser
```

For a managed profile, use the actual manifest and package-relative config:

```sh
cargo proofs preview --draft --manifest-path <version>/Cargo.toml \
  --proofs-config aeneas/profiles/<profile>/proofs.toml --no-browser
```

Substitute real paths. `--proofs-config` stays inside the selected package and is
supported only with `--draft` in the inspected CLI. Draft mode requires Node.js 24+,
makes no service requests, and uses no credentials or recorded run. Inspect the
rendered prose, code fences and associations, then stop the server. Describe this
as a rendering/schema check, never a formal proof or publication validation.
