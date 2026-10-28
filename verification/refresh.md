# Refreshing evidence after input changes

A new hash is a new proof input. Preserve existing manifests, sessions, solver outputs, and captures; do not edit their hashes to match the working tree. The translation and subsequent documentation/skill corrections require fresh verification. Current outcomes and immutable bundle identities are recorded in each version’s status page.

## Choose the verifier

For Aeneas, use the version-local managed setup/verify wrappers, regenerate and
compare all maintained models, run native checks separately, rebuild/audit Lean
and compare fingerprints. Save a new local archive and scoped summary using the
[publication guide](publication.md). Do not activate the Creusot environment or
rewrite old evidence hashes. The remaining instructions are for Creusot only.

## Creusot environment prerequisite

Use either the pinned Linux environment described in [README](../README.md) or the native macOS arm64 installation in the [local setup guide](local-macos.md). Activate with `source scripts/activate.sh`, which selects the host environment, and validate the installation before running per-version workflows. Activation does not install missing tools. x86_64 is not required.

The project runners support the local tool paths and portable archive promotion. httpdate’s macOS `SystemTime` assumptions are recorded in its platform review and ledger. Use Bash 4 or newer for the runners. A successful bootstrap proof is separate from crate evidence.

## Freeze and run

Finish changes to contracts, scopes, assumptions, inventories, guides, and skills before capturing inputs. Check each runner's input list; post-run result pages must not be proof inputs. Creusot status owners are httpdate's `verification/coverage.md` and form_urlencoded/percent-encoding's `verification/results.md`. Aeneas status is per-profile results.md and evidence/summary.json.

The version-local procedure for httpdate is documented in [its README](../httpdate/1.0.3/README.md). Its formal and correspondence runners preserve the old latest directories under unique historical names before promoting complete replacement bundles. The native correspondence workflow can run independently before or after formal proof. After both pass for matching inputs, run `capture-correspondence.py --bind RUN_DIRECTORY` in the activated verification environment to bind the native result to the new formal manifest. Audit the new proof with independent root reconstruction and the complete generated inventory.

For form_urlencoded, run `bash form_urlencoded/1.2.2/scripts/verify.sh` from the
repository root for standard Why3find verification. Independently audit the new
immutable bundle; `latest` advances only on success. The direct workflow and
`latest-direct` records are historical and must not be substituted for this run.

Before refreshing percent-encoding, review the new form_urlencoded manifest and
update `FORM_EVIDENCE` and `FORM_EVIDENCE_SHA256` in its `scripts/check-proofs.py`,
plus the reviewed scope and identity in `verification/dependency-ledger.md`.
The current `scripts/verify-why3find.sh` reads FORM_EVIDENCE from check-proofs.py;
do not update the obsolete hard-coded path in the historical direct `verify.sh`
as though that selected the standard runner's dependency.

Pin the immutable manifest, not a moving latest link. Freeze inputs, then run
`bash percent-encoding/2.3.2/scripts/verify-why3find.sh` from the repository root.
It performs native checks and standard formal verification with matching input
fingerprints. Independently audit the new archive and update the results page.

## Close out

Update the status owners only after checking the actual manifests, complete target inventories, positive root counts, open/excluded classifications, native logs, and before/after fingerprints. Check navigation and scope documents for stale provisional statements, without copying run counts into them. Retain exact links to the new immutable bundles and describe any remaining refresh blocker. Verify that status-page edits did not change a fingerprinted input; if they did, another fresh run is required.

This process is local evidence production. proofs.rs recording and publication are separate operations and are not authorized by a refresh request.
