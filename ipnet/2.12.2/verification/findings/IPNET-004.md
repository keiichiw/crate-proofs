# IPNET-004: Raw subnet constructors defer invalid-prefix failure

## Identity and classification

- ID: `IPNET-004`
- Crate/version: `ipnet/2.12.2`
- Component: release implementation
- Kind: `specification-question`
- Confidence: source-reviewed migration of the linked record; reproduction claims are those of the original investigation
- Resolution: `not-a-bug` for the pinned investigation, not a statement about latest upstream
- First observed / last reproduced: not independently established during this migration
- Upstream report: no new report made; original reporting status is in the source record
- Upstream fix: not checked during migration

## Pinned inputs

The maintained [source lock](../../source.lock.json) has SHA-256 `be13258bb37c10646d281752b5148152d9949aecdb37c1c22f4376d77278d31c`
and pins release archive `791930b43c0d5973160d90a8f3894509f2b273430f5c5c73b668636d0287c5c0`. This identifies the maintained release,
not every original execution setting. Original profile, host/target, features,
compiler/tool revisions and debug/release settings are authoritative only where
specified by the linked record or its immutable manifest. Unspecified values remain
unknown; no current tool installation is substituted for historical identity.

## Expected behavior and its basis

Only valid prefixes are within the selected enumeration contract; nonempty q>32 is a separately specified panic domain.

The linked original analysis supplies its documented or independently desired
contract and domain. A stronger desired total-success law must not be represented
as a documented no-overflow promise.

## Observed behavior

Nonempty IPv4 range q=33 or 255 panics; empty reversed range returns None; q=32 succeeds.

## Reproduction

The historical raw-iterator inputs and outcomes are preserved in the original
record identified below. No schema-check command reproduces this iterator behavior.
Use that original record for historical reproduction conditions; the current proof
contracts distinguish valid enumeration from the invalid-prefix panic domain.

Last independently rerun: not rerun while formatting this finding. The original
reproducer and evidence are retained unchanged. For a new replay use unchanged
pinned source and a fresh ignored .work output, record commands/input hashes and
exit status, and append a dated observation. Minimized-case claims are limited to
what the original record actually checked.

## Evidence and interpretation

- [Archive descriptor](../../aeneas/profiles/default/evidence/archive.json), archive SHA-256 `4b678894a4b096b2e0ed6d4b33731066a968b01cc7a999bd1bfe8e5ff73780c9`, exact member `payload/legacy/verification/bugs/README.md`, record SHA-256 `7fa0d923c714d8e78f214fdec12c8ad48cdf213b290146edb9dfd32f72eeea02`. Availability: local-only; no public retrieval URL.

These are historical native observations, source review or translation diagnostics
as classified above, not new Lean theorem coverage or an independent rerun.
The original record's caveats take precedence over this navigation summary.

## Cause, impact and proof scope

Known raw-input/domain behavior, explicitly not a newly discovered valid-input algorithm bug.

Only affected APIs/types/configurations actually identified by the sources are
covered. Do not infer latest-upstream status, all widths, other targets or async
execution from a bounded observation. Native failures and formal proof exclusions
are separate; preserve the original desired contracts and their guarded proof domains.

## Resolution and regression

No release source or frozen evidence is changed by this migration. Retain the
counterexample, successful controls, input/state/consumption checks and the original
scope restrictions as regression requirements. A proposed source/tool fix must be
reviewed and checked separately at a pinned revision. No issue submission, push,
publication or new proof acceptance is performed here.
