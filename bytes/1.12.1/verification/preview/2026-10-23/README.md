# bytes 1.12.1: local Run and Finding preview

This session keeps three observations separate:

1. Managed verification re-extracts all nine models, builds Lean, audits the named
   roots and executes the native suites and mandatory tool regressions.
2. `cargo proofs run --local -- ...` records a fresh standard Lake build and the
   CLI's standard Lean theorem/axiom extraction as SARIF. Repository setup logs and
   the bug reproducer are not promoted to formal SARIF checks.
3. `findings.json` contains one unpublished Finding creation payload. Its native
   counterexample does not assert a successful proof of the affected signed APIs.

## Source and local recorder

The CLI's normal recording path requires a clean, pushed GitHub source commit.
The current proof profile has not been pushed. The normal record wrapper was
tried and stopped at that check. Nothing was pushed to make the check pass.

A clean, detached local clone at commit
`f576a7aefada20482271bbadf1dc1ee7be72c0c0` is retained in
`../../../.work/preview-session/source`. It contains the maintained bytes profile;
current edits in the caller's working tree are not silently added to its claims.
This is a local, unpublished source identity, not an accessible GitHub revision.

The experimental recorder is copied from the profile's pinned, patched CLI.
`local-recorder.patch` records the additional local mode and preview-sidecar code.
The original selected tool cache and profile tool locks are unchanged. The
experimental build is isolated under `../../../.work/preview-session/recorder`.
It is not an installed or released cargo-proofs feature.

Local recording still uses the immutable detached-checkout boundary, preparation
identity checks, standard Lake build, formal extraction, axiom restrictions, and
post-execution source checks. It adds `properties.proofs.localOnly=true`, records a
`file://` source identity, and refuses to upload or publish that evidence before
any authentication or upload request. The standard recording path retains its
published-source requirement. Local files are stored under the explicit
`PROOFS_RECORD_DIR` in this session, without changing user tool homes.

## Finding

- [Creation payload](finding.json), or [array for preview](findings.json)
- [Fresh native invocation and input/output hashes](record.json)
- [Observed output](stdout.txt) and [stderr](stderr.txt)
- [One-byte desired-contract assertion](minimal/src/main.rs), [fresh invocation](minimal.record.json), and [assertion failure](minimal.stderr.txt)
- [Existing finding](../../../verification/findings/BYTES-001.md)

The one-byte assertion independently fails with `Ok(255)` versus `Ok(-1)` and
exit code 101. The comprehensive control reproducer exits 0 because it asserts
the observed discrepancy as well as consumption controls.

The counterexample was freshly reproduced on macOS arm64 with Rust 1.91.1 and
`default-features=false`. For all-`0xff` input, widths 1..7 produce positive values
from `try_get_int`, `try_get_int_le`, and `try_get_int_ne`, while their non-`try`
counterparts return -1. Width 8 is a successful control. All six variants consume
exactly the requested bytes. The reproducer forbids unsafe code. Its exit 0 means
its assertions successfully observed the bug and the controls; it does not mean
the signed-return contract holds.

The payload uses the service's required content fields and an empty optional API
ID list. The affected API names are explicit in the content. API IDs must only be
added after resolving them against the discovery Report's exact release. No
Issue or PR was created or inferred. Latest upstream status has not been checked.

In the browser this is **Local Finding draft · Not submitted**. It has a local
anchor and no invented public Report ID, Finding ID, revision, or event history.
After a publishable Report exists and publication is explicitly authorized, its
creation payload can be included in the initial Report request or sent to
`POST /api/v1/reports/:id/findings` with an idempotency key. Subsequent links and
status edits belong to the Finding APIs, not a Report revision.

## Result

Successful local-only Run: `29ae1f77-352a-486c-a5ce-4818ca5d2a72`,
with 56 formal Claim contracts and 56 passing standard CLI checks. The separate
managed verifier passed all 161 named roots and nine model comparisons on
`aarch64-apple-darwin`. See [recorded-run.json](recorded-run.json),
[managed-verification.json](managed-verification.json), and
[browser-check.json](browser-check.json). Public API catalogue metadata could not
be matched for every API, so those preview warnings remain explicit.

The preview is at <http://127.0.0.1:58693/report#findings> while its local server
is running. The Finding is a local draft, not an entry on the public service.
No issue, push, login, upload, or publication was performed.

## Reopen the preview

From this repository:

```sh
bash bytes/1.12.1/verification/preview/2026-10-23/start-preview.sh
```

The launcher uses the retained experimental binary, source snapshot, recorded Run,
and Finding sidecar. It prints a localhost URL. Add `--port 8080` for a fixed port.
Editing `findings.json` and reloading changes the draft without rerunning the
verifier. The sidecar is checked against the actual service creation schema.
Preview is read only and uploads nothing. The local-only Run remains ineligible
for publication.

## Recorder compatibility findings

The first local attempt built Lean successfully but the CLI refused API discovery
at `cfg(loom)`. That Run remains unsuccessful, with zero certified contracts;
see [attempt1.json](attempt1.json). It was not edited into a success.

The experimental recorder recognizes name-only Cargo `check-cfg` declarations as
known flags without enabling them. It rejects build-script/custom Cargo config and
extra Rust-flag cases rather than assuming an unknown cfg value. It also recognizes
Miri's flag, generic inherent methods and actual default trait method bodies;
required trait signatures without bodies remain excluded.

[api-aliases.json](api-aliases.json) explicitly bridges 31 historical labels to
unique Rust declarations; 25 labels resolve directly. Each bridge is bound to the
release source file SHA-256 and exact AST source span. Specializations of inherited
default methods point to the actual trait default body; they retain the original
Lean theorem, module, precondition and formal input types. This is manual binding
metadata, not a new proof of the Rust-to-Lean translation. The table is included in
the Run's Aeneas configuration and only accepted for local-only recording.

All 56 mappings are kept. Tampering with a bridge's source hash, span, callable,
legacy label or package containment is tested as rejection. No unsupported API
is silently omitted to obtain a successful Run. The temporary recorder changes
are retained as a patch here; the selected pinned tool cache is unchanged.
