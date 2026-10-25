# Managed Aeneas runner

The bytes 1.12.1 target imports the managed runner from the develop branch.
Existing main-branch crates keep their own layouts and commands; this addition
does not migrate them or certify new platforms.

## Commands

From the repository root:

```sh
python3 scripts/aeneas-manage.py lint bytes/1.12.1
python3 scripts/aeneas-manage.py check-source bytes/1.12.1
bash bytes/1.12.1/scripts/setup.sh
bash bytes/1.12.1/scripts/verify.sh
```

`lint` checks configuration and theorem/API inventory consistency. `check-source`
checks already restored source against the complete source lock. Neither proves
contracts. Setup restores pinned source and tools; `--sources-only` restricts it
to source restoration. `--offline` requires existing caches.

The version-local `aeneas/profiles.toml` selects a profile. Its `verification.json`
configures native checks, extraction checks, the Lean package, theorem inventory
and report mapping. Verify runs the configured pipeline, records input identities
before and after, builds Lean and audits theorem dependencies. Native checks,
compiler regression controls and formal theorems remain distinct evidence.

## Immutable inputs and local caches

Source archives are checksum-pinned with complete file/mode inventories and are
restored to the version's ignored `.work/source`. Unexpected source changes fail
validation. Tools are pinned by revisions, patches, resulting trees, OCaml packages
and runtime identities. Shared installations live in ignored `.work/tools` at the
repository root; build outputs and run logs remain version-local.

The bytes profile requires core, numeric and stage3 extractors and the ordinary
negative control. Their compiler patches are trust boundaries; setup/build success
does not prove those transformations correct. Do not replace locks or generated
Lean when editing report prose.

`AENEAS_TOOL_CACHE` and `AENEAS_ARCHIVE_CACHE` can select absolute cache paths.
Interactive `scripts/env.sh` activation is version-local. Do not mix it with the
Creusot environment. Setup may require installed Rustup, Elan, OCaml/opam, GNU make,
a native compiler, pkg-config and GMP; `doctor` checks prerequisites.

## Historical evidence and publication

Each profile's results distinguish accepted original inputs from current edits.
The bytes archive descriptor points to a local-only content-addressed archive.
`scripts/aeneas_evidence.py` checks and restores archived records without changing
their identities. A checksum check is not a new theorem audit.

Historical `upstream/`, `.tools`, `/workspace` and preview URLs in retained records
identify old runs. Use the version README for current commands. A new report input
fingerprint requires fresh verification before claiming acceptance for that input.
No setup, lint, source check or verification command authorizes publication.
