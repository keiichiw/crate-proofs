# IE-D2: FixedInt overview and method endian descriptions disagree

## Identity and classification

- ID: `IE-D2`
- Crate/version: `integer-encoding/4.1.0`
- Component: release implementation
- Kind: `documentation-mismatch`
- Confidence: source-reviewed migration of the linked record; reproduction claims are those of the original investigation
- Resolution: `open` for the pinned investigation, not a statement about latest upstream
- First observed / last reproduced: not independently established during this migration
- Upstream report: no new report made; original reporting status is in the source record
- Upstream fix: not checked during migration

## Pinned inputs

The maintained [source lock](../../source.lock.json) has SHA-256 `cf254d85dd4e0016dbb95013f15de448f2a2415de98b7a07c5e104e11fd6d6f3`
and pins release archive `14c00403deb17c3221a1fe4fb571b9ed0370b3dcd116553c77fa294a3d918699`. This identifies the maintained release,
not every original execution setting. Original profile, host/target, features,
compiler/tool revisions and debug/release settings are authoritative only where
specified by the linked record or its immutable manifest. Unspecified values remain
unknown; no current tool installation is substituted for historical identity.

## Expected behavior and its basis

The overview and detailed methods should consistently describe the same byte order.

The linked original analysis supplies its documented or independently desired
contract and domain. A stronger desired total-success law must not be represented
as a documented no-overflow promise.

## Observed behavior

The overview says machine endianness; detailed methods say little-endian and recorded built-in observations are little-endian.

## Reproduction

Exact invocation, working directory, exit status and reproducer identities must be read from the original record and its adjacent fixture/manifest. They are not reconstructed from a filename here. If unavailable, these fields remain unknown; do not run historical commands against missing paths or overwrite fixed baselines.

Last independently rerun: not rerun while formatting this finding. The original
reproducer and evidence are retained unchanged. For a new replay use unchanged
pinned source and a fresh ignored .work output, record commands/input hashes and
exit status, and append a dated observation. Minimized-case claims are limited to
what the original record actually checked.

## Evidence and interpretation

- [Original record](../../aeneas/profiles/default/native-findings.md), SHA-256 `af58150a96a980e0af86507342d979f336cc69e4e231f42351ac82e8ef821b05`. Distributed tracked document; embedded historical paths may need restoration.

These are historical native observations, source review or translation diagnostics
as classified above, not new Lean theorem coverage or an independent rerun.
The original record's caveats take precedence over this navigation summary.

## Cause, impact and proof scope

Documentation inconsistency; native tests do not establish all-host behavior.

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
