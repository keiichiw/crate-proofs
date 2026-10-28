# Writing findings

## Prepare an issue-ready finding

Use the existing [github-issues skill](https://github.com/github/awesome-copilot/blob/main/skills/github-issues/SKILL.md)
for issue writing. Read an installed copy when available; otherwise read its
remote `SKILL.md` and relevant
[template reference](https://github.com/github/awesome-copilot/blob/main/skills/github-issues/references/templates.md).
Resolve needed references relative to that skill's location. Use available GitHub
read tools or a read-only browser/CLI fallback; its named MCP tools may be absent.
Invoke drafting only, not the issue-creation step. Do not install or copy the entire
skill incidentally. If it cannot be read, disclose the dependency gap rather than
claiming to have followed it.

Identify the actual upstream repository from package metadata and source pins.
Inspect its issue instructions and templates: `.github/ISSUE_TEMPLATE/` Markdown
templates, YAML issue forms and `config.yml`, legacy `ISSUE_TEMPLATE.md` locations,
and contribution instructions. Use the current upstream default branch or record
the revision inspected; a release archive may lack the current template. Check for
related existing issues and link a known match without inventing an upstream report.

Use an applicable upstream template in preference to the generic templates in
`github-issues`: this explicit repository rule overrides that skill's generic
template rule. Preserve required headings/questions and order. For YAML forms,
turn labels/prompts into Markdown sections and answer required fields/selections
from evidence; retain the field mapping if later filing requires it. Do not claim
checklist steps were performed unless they were. If no applicable upstream template
exists, select the matching `github-issues` template. If upstream is inaccessible,
mark the draft as pending template alignment instead of assuming no template exists.

Write the title and body so they can be used as an upstream GitHub issue without
rewriting. Explain the observation in the upstream project's terms. Include minimal
reproduction code/commands inline or accessible references; avoid local-only paths,
unretrievable archives and proofs.rs-specific instructions. State evidence gaps.
For ambiguity or a precondition, choose a question/documentation issue shape without
asserting a confirmed bug. Do not invent an issue for a purely internal observation
that adds nothing beyond the report. Preparing this content never authorizes filing.

## Reproduce entirely in Rust

For Rust crate findings, provide a self-contained Rust code snippet and the Cargo
dependencies needed to run it. All steps that demonstrate the discrepancy must
execute in Rust; do not require Python scripts, pip packages, another language's
validator, intermediate exported data files or a separate checker. Ordinary Cargo
commands to build and run the snippet are appropriate.

Exercise the actual crate API. For schema findings, generate the real schema and
validate it with a Rust JSON Schema library rather than copied regular expressions
or a hand-written evaluator. Pin relevant dependencies, use only needed features
and keep the reproducer focused on the reported symptom. Make clear whether an
assertion expresses expected correct behavior and fails, or asserts the observed
discrepancy and succeeds. Remove unused future regression modes. Compile and run
the exact published snippets when checking a new or modified reproduction; report
an inability to execute them rather than claiming reproduction from source alone.

## Keep verification details out of findings

Finding titles and bodies, including the reusable GitHub issue draft, describe
observable crate behavior and ordinary reproduction. Do not include verification
setup, verifier/solver/Lean versions, extraction or model-generation steps, proof
profiles, theorem or audit counts, proof commands, proof-run dates, toolchain
patches for verification, or descriptions of how the proof investigation found
the behavior. Keep that provenance in the report's appropriate fields or separate
internal evidence, not in the finding narrative.

Include ordinary execution conditions only when needed to reproduce or distinguish
the behavior: affected crate version, Rust version, features, OS/architecture and
debug/release settings. An upstream template's Environment section follows this
same rule; it is not a reason to insert the verification environment. Explain the
expected result from public API documentation or the relevant behavior, rather
than making the reader interpret formal contracts or proof infrastructure.

## Public report drafts

A finding adds a concrete observation: an unexpected result, useful precondition,
specification ambiguity, unsupported boundary or bug. Failure to prove something
alone is not a bug. Do not repeat the report's overview, assumptions and exclusions
as separate findings. Use an informative English plain-text title and a
self-contained Markdown body following the upstream template selected above.

```toml
[[report.findings]]
title = "One-byte signed reads return a positive value"
body = '''
Describe the affected version/API, concrete input and observed result here.
Explain the expected behavior and its independent basis, the conditions of the
ordinary reproduction, and the exact actual result.
'''
# Optional: use real, uniquely resolvable public paths for this crate/version.
# api_paths = ["example::Reader::read"]
```

The example is a writing scaffold, not evidence for an actual bug. When a bug is
claimed, include a compact runnable reproducer, expected/actual result and relevant
features/target/build conditions. For other observations, explain the supporting
contract or diagnostic without inventing a reproduction. Keep enough context in
the finding itself; an upstream link can carry longer investigation and fix discussion.
Replace the scaffold with the actual template sections. Reuse the approved
issue-ready title/body in `report.findings`, preserving fences, links and premises.
If template-complete content exceeds service limits, retain the full issue draft
under the owning version and flag the size conflict; do not silently drop required
information or call a shortened summary ready for direct issue submission.

The inspected CLI accepts only `title`, `body` and optional `api_paths` on each
`report.findings` entry. It allows up to 20 findings on initial publication, with
nonempty title/body of at most 1,000/10,000 UTF-16 code units respectively after
trimming, and at most 50 nonempty API paths per finding. Each path must resolve
uniquely in the report's crate/version; aliases are deduplicated. Do not add internal
classification, resolution, evidence-link or upstream-status keys to this table.
Recheck the pinned schema when using a different CLI.

Findings are independent of claims: an affected API may have no proof, and a bug
does not automatically invalidate a claim whose contract excludes the failing case.
Review that relationship internally and explain material proof-scope implications
in the report, rather than adding proof discussion to the finding.
Group counterexamples with a common cause;
do not inflate the number of bugs by width, target or profile.

## Initial publication versus existing findings

`[[report.findings]]` seeds findings only when a report is first published. Updating
an existing report leaves its published findings unchanged. Ordinary preview of an
existing report shows the published findings; draft preview shows the local draft.
TOML edits are not a synchronization mechanism for published findings. If the request
concerns a published finding, prepare the exact proposed edit and identify the
report/finding; changing it through Web/API needs explicit authorization.

Keep local confidence/resolution distinct from the public service's validity and
upstream status. Do not infer that an issue was reported, a PR merged or a fix
released from a local workaround. The service supports these as separate metadata
with evidence requirements; consult the matching `book/src/findings.md` and schema
before an authorized external update.

## Crate-local investigation records

Follow [the repository storage policy](../../../../verification/findings.md) and
[template](../../../../verification/templates/finding.md). Store a new record at
`<crate>/<version>/verification/findings/<ID>.md`, or under the owning nested
independent workspace. Choose a stable crate-local ID after inspecting existing
records and link it from that target's README or results.

Retain source identity and digests, classification, confidence and resolution,
expected behavior and its basis, exact observed input/output/state, first failing
stage, controls, ordinary reproduction cwd/command/exit status and evidence
availability. Retain verification-environment provenance in separate internal
evidence and reference it from record metadata when needed; do not copy it into
the finding narrative or reusable issue body. Distinguish a historical command needing restored inputs from one
that is runnable now. Do not describe source-reviewed reasoning as reproduction.

Check in the short record and minimal reproducer. Keep complete logs and repeated
models in ignored `.work` or the checked local archive scheme. Follow
[publication policy](../../../../verification/publication.md) for archive descriptor,
digest, exact member and availability. A local-only hash is not a download link.
Do not rewrite frozen historical evidence: append dated updates or wrap it with a
new scoped record linking the original. No cross-crate counts/status tables or
implicit upstream reporting/publication belong in this workflow.
