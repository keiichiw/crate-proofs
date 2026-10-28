---
name: proofs-report-writing
description: Write or review proofs.toml reports and verification findings in crate-proofs using pinned evidence and accurate proof scope. Covers reader-facing report.findings and crate-local investigation records; use the verifier-specific skills for proving contracts.
---

# Proof reports and findings

Produce reviewable local drafts grounded in the target's actual contracts and
evidence. Write reader-facing report prose and findings in English, following the
repository's existing convention, unless the user requests another language.

## Relationship to the official guide

Use [Write a useful report](https://proofs.rs/book/write-a-report) and its
[write-proofs-report skill](https://github.com/proofs-rs/proofs-rs/tree/main/skills/write-proofs-report)
as the shared editorial foundation. Read that skill when drafting report prose:
use the matching local proofs-rs checkout's `skills/write-proofs-report/SKILL.md`,
or fetch the linked skill and its needed references. This repository skill adds
crate/version evidence handling, issue-ready findings and the author/reviewer
workflow below. For accepted configuration and rendering, check the pinned CLI
rather than assuming the latest guide matches it. If a remote source cannot be
read, use matching local sources and disclose which version was consulted.

Report body fields and finding bodies support Markdown; titles are plain text.
See [report guidance](references/proofs-toml.md) for formatting details.

## Establish the target and evidence

1. Read the repository and target version/workspace `AGENTS.md`. Locate the selected
   Cargo package, managed profile or subject, its configured report path, and any
   existing report. Do not assume `proofs.toml` lives beside the outer manifest.
   Keep crate-specific drafts, reproductions and evidence under `<crate>/<version>/`.
2. Read the specification, current results, theorem/API inventory, source/tool
   locks and relevant evidence summaries. Inspect original logs or theorem statements
   when a claim needs them. Record which source, host/target, features, profile and
   run support each substantive assertion. Unknown inputs remain unknown.
3. Distinguish unchanged release bodies from a verification fork or adapter, native
   tests from checked formal contracts, and preserved historical acceptance from a
   fresh run. File existence, successful extraction and a build alone do not establish
   API correctness. Do not turn helper theorem counts into API coverage counts.
4. Preserve established contracts and tool configuration. If evidence and intended
   prose disagree, narrow the prose or identify the unresolved claim; do not weaken
   the contract or invent a successful result. Writing alone does not require a new
   proof run. For requested proof work, use the appropriate repository skill and the
   target's activation; never mix Creusot and Aeneas environments.

## Choose the deliverable

- For `proofs.toml`, read [report guidance](references/proofs-toml.md). Describe the
  observable guarantee, its premises, trust boundary and exclusions in their proper
  fields. Keep API/theorem mappings aligned with the actual inventory.
- For a reader-facing observation, read [finding guidance](references/findings.md)
  and use `[[report.findings]]` for an initial report draft. Use the linked
  `github-issues` skill and upstream issue templates to produce a title and
  Markdown body directly reusable as a GitHub issue. A useful precondition,
  ambiguity or boundary can be a finding without being a bug. Keep finding prose
  about observable behavior and ordinary reproduction; omit verification tools,
  proof environments, audit results and proof-development details.
  Lead with the unmet property and affected APIs, followed by a short Rust snippet
  for one representative API. Usually list only necessary dependencies/features,
  not a full Cargo manifest or exhaustive experiment. Do not require Python or a
  second-language checker. Follow the minimal-example guidance in the reference.
- For a retained investigation or counterexample, use the same finding guidance
  and the repository's [storage policy](../../../verification/findings.md) and
  [record template](../../../verification/templates/finding.md). This is a separate,
  more detailed record; do not force its headings into the public finding body.

Write only the requested artifacts. Creating a public-facing TOML finding does not
by itself require a new investigation file. When both exist, keep their scope and
observations consistent without copying every internal detail into the report.

## Delegate prose and correctness separately

For human-readable `proofs.toml` content, use separate writing and correctness
agents. This workflow explicitly calls for subagents when delegation is available.

1. The primary assembles target paths, source/run identities, contracts, mapped
   APIs, assumptions, exclusions and unresolved evidence into an evidence packet.
   Keep specification design and proof implementation separate from prose drafting.
2. Delegate `report.title`, `explanation`, `trusted_assumptions`, `limitations`,
   `environment` and finding titles/bodies to a model strong at prose, preferably
   GPT-6.1 Terra (`gpt-6.1-terra`) or the user's chosen writing model. Provide the
   official report-writing skill, this skill and raw supporting artifacts. Limit
   edits to editorial fields; preserve mappings, tool settings, contracts and
   evidence. For findings, also provide the issue skill and upstream template.
3. Use a separate strong reasoning model, preferably GPT-6 Astra (`gpt-6-astra`) or
   the user's chosen reviewer, to check the draft against raw contracts, source and
   evidence. Review mathematical meaning, release correspondence, premises, trust
   boundaries, proof versus tests, coverage and freshness. Provide artifacts to
   inspect, not just the writer's summary or a proposed verdict.
4. Have the writer revise substantive review findings and the reviewer recheck
   changed claims. The primary checks the final diff, commands, evidence identities
   and coverage claims and delivers the result with material remaining gaps.

Choose from models actually available; these names are role preferences, not
availability guarantees. Select models explicitly when supported. If the preferred
model or delegation is unavailable, disclose the fallback and distinguish self-review
from independent review. Never claim a model or reviewer was used when it was not.

## Validate the final artifact

- Parse edited TOML with Python 3.11+ `tomllib` or the installed CLI. Syntax parsing
  checks no proof claims and does not establish CLI schema validity.
- Check the installed/pinned CLI schema before adding fields. Prefer its matching
  local source/docs (`cli/src/config.rs`, `cli/README.md`, `book/src/findings.md` in
  the proofs-rs checkout located via target setup/tool locks). Do not silently
  upgrade a pinned CLI to gain draft or mapping features.
- When supported and useful, run `cargo proofs preview --draft` with the selected
  manifest/config and inspect the rendered report and findings. Draft preview is
  unverified and supplies no evidence. For Aeneas, check ordered API/theorem/module/
  precondition entries against the inventory; use the target's audit procedure when
  formal audit is requested, rather than calling metadata comparison a proof.
- Review the diff for inflated guarantees, unexplained premises, stale run dates,
  broken evidence links and invented publication/upstream status. Report what was
  validated and what remains unsupported.

Do not log in, push, publish, deploy, contact upstream or change published findings
without explicit authorization. `publish --dry-run` authenticates and may import a
remote API catalogue; use draft preview for ordinary local prose review.
