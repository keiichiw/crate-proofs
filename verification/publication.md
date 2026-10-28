# Publication contents

Git contains reproducible verification inputs and compact, scoped result summaries.
Raw execution logs and repeated input/generated snapshots belong in ignored local
archives, not the source tree. Packaging evidence does not rerun a proof and does
not certify the current checkout merely because an earlier run passed.

## Distributed files

Keep specifications, authored proofs, target-specific generated Lean, source/tool
locks, ordered patches, verification configuration, scripts and regression tests in
Git. Every managed profile has `evidence/summary.json` with the original result,
host/target, named theorem audit, input fingerprint digests and archive references.
`evidence/archive.json` identifies the complete original execution records by
SHA-256 and names their ignored local store. It explicitly says `local-only`, with
no public download URL. A fresh clone can rerun verification, but cannot download
these private archives from their hashes alone.

Each profile’s results.md and evidence/summary.json report preserved acceptance
for the original inputs. Native tests, exact extraction comparisons, standard Lake
build, axiom audit and before/after identity checks have distinct meanings. macOS
arm64 results do not certify Linux. See each profile's specification and results
for API coverage, preconditions, exclusions and trusted models.

## Current test inputs and archived provenance

Normal managed verification uses current source/tool locks, capture harnesses,
mathematical oracles, regression configurations, specifications and proof packages.
It does not reconstruct inputs from historical file lists, old Git commits,
successful CSVs or evidence archives. Configured fixtures and theorem/API registries
are current runtime inputs; archived execution records are provenance only.

Original acceptance summaries and archive descriptors remain provenance for their
original inputs. Findings identify archived originals by descriptor, exact member
and SHA-256. Local-only archives are not retrievable from a checksum alone and are
never a prerequisite for setup or verification. Reader-facing historical documents
and navigation indexes are not maintained. Fresh proof success still requires
native checks, extraction equality, standard Lake build, axiom audit and unchanged
before/after fingerprints.

## Save, inspect and restore evidence

Normal setup/verify writes only to ignored `.work/` directories and never publishes.
Save a complete run explicitly after checking its scope:

```bash
python3 scripts/aeneas_evidence.py archive ipnet/2.12.2/.work/runs/RUN \
  --store ipnet/2.12.2/.work/evidence-archives \
  --descriptor ipnet/2.12.2/.work/RUN.archive.json
python3 scripts/aeneas_evidence.py summarize ipnet/2.12.2/.work/runs/RUN \
  --descriptor ipnet/2.12.2/.work/RUN.archive.json \
  --store ipnet/2.12.2/.work/evidence-archives \
  --output ipnet/2.12.2/.work/RUN.summary.json
```

Both output files must be new. The summary command checks the archive, matches the
run bytes to its members, checks every original artifact hash, and requires passed
pipeline/audit records and equal input fingerprints. It summarizes those records;
it does not independently prove a theorem or create a SARIF success.

To inspect a retained profile archive, use the store named in its descriptor:

```bash
python3 scripts/aeneas_evidence.py verify \
  ipnet/2.12.2/aeneas/profiles/default/evidence/archive.json \
  --store ipnet/2.12.2/.work/evidence-archives
python3 scripts/aeneas_evidence.py restore \
  ipnet/2.12.2/aeneas/profiles/default/evidence/archive.json \
  --store ipnet/2.12.2/.work/evidence-archives \
  --destination ipnet/2.12.2/.work/restored-evidence
python3 scripts/aeneas_evidence.py check \
  ipnet/2.12.2/aeneas/profiles/default/evidence
```

Restore refuses an existing destination. Checksums, complete file inventory,
relative paths and modes are verified before the restored tree is installed.
The `check` command needs no local archive: it rejects unlisted files (including new
logs) and altered/missing compatibility fixtures in a distributed evidence tree.
The manual native CI workflow runs these checks before tool installation. Evidence
directory ignore rules prevent accidentally staging new raw artifacts; adding a new
compatibility fixture requires reviewing its inventory and explicitly staging it.
Archive member references begin with `payload/`; `container_member` identifies an
inner historical tar archive when present. No path implicitly fetches an archive.

For a future release, an explicitly authorized publication can attach the complete
archive and publish its digest and retrieval URL. The local packaging commands have
no network or upload operation. Keep setup/native/custom-check logs and repository
script/patch bodies out of SARIF; only standard tools and CLI standard audits supply
formal recording results. proofs.rs registration remains a separate operation.

## Documentation maintenance

Current guides and AGENTS may be fingerprinted inputs. Updating their prose does
not refresh a prior proof run. Preserve original evidence hashes and report the
old run against its archived inputs; only a new complete verification can establish
acceptance for changed current inputs. Archived originals remain immutable. Retired reader
documents are not maintained as part of the current documentation.
