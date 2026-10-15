# Refreshing evidence after input changes

A new hash is a new proof input. Preserve existing manifests, sessions, solver outputs, and captures; do not edit their hashes to match the working tree. The translation and subsequent documentation/skill corrections require fresh verification. Current outcomes and immutable bundle identities are recorded in each version’s status page.

## Environment prerequisite

Use either the pinned Linux environment described in [README](../README.md) or the native macOS arm64 installation in the [local setup guide](local-macos.md). Activate with `source scripts/activate.sh`, which selects the host environment, and validate the installation before running per-version workflows. Activation does not install missing tools. x86_64 is not required.

The project runners support the local tool paths and portable archive promotion. httpdate’s macOS `SystemTime` assumptions are recorded in its platform review and ledger. Use Bash 4 or newer for the runners. A successful bootstrap proof is separate from crate evidence.

## Freeze and run

Finish changes to contracts, scopes, assumptions, inventories, guides, and skills before capturing inputs. Check each runner's input list; post-run result pages must not be proof inputs. Current status owners are httpdate's `verification/coverage.md` and the other versions' `verification/results.md`.

The version-local procedure for httpdate is documented in [its README](../httpdate/1.0.3/README.md). Its formal and correspondence runners preserve the old latest directories under unique historical names before promoting complete replacement bundles. The native correspondence workflow can run independently before or after formal proof. After both pass for matching inputs, run `capture-correspondence.py --bind RUN_DIRECTORY` in the activated verification environment to bind the native result to the new formal manifest. Audit the new proof with independent root reconstruction and the complete generated inventory.

For form_urlencoded, run the expanded direct workflow described in [its coverage guide](../form_urlencoded/1.2.2/verification/coverage.md). It creates a unique bundle and advances `latest-direct` only on success. Independently audit the new immutable bundle. Keep the earlier `latest` byte-core evidence distinct.

Before percent-encoding runs, review that newly audited form_urlencoded bundle and update all of the following together in `percent-encoding/2.3.2/`:

- `scripts/check-proofs.py`: `FORM_EVIDENCE` and `FORM_EVIDENCE_SHA256`.
- `scripts/verify.sh`: the dependency audit manifest path.
- `verification/dependency-ledger.md`: the reviewed manifest identity, hashes, and scope.

Pin the immutable bundle, not just the moving `latest-direct` link. Update these pins only after a new passing dependency bundle exists. Then freeze percent-encoding inputs, run the native full-scope workflow, and run the formal workflow documented in [its results](../percent-encoding/2.3.2/verification/results.md). Both must use matching source fingerprints. Audit the new archive independently.

## Close out

Update the status owners only after checking the actual manifests, complete target inventories, positive root counts, open/excluded classifications, native logs, and before/after fingerprints. Check navigation and scope documents for stale provisional statements, without copying run counts into them. Retain exact links to the new immutable bundles and describe any remaining refresh blocker. Verify that status-page edits did not change a fingerprinted input; if they did, another fresh run is required.

This process is local evidence production. proofs.rs recording and publication are separate operations and are not authorized by a refresh request.
