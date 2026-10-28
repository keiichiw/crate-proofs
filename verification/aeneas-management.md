# Managed Aeneas crates

Migration is sequential: restore source, preserve contracts, check native tests,
regenerate models, rebuild/audit, and then accept a target-specific run.
Aeneas workspaces use this layout, with named profiles where needed. Consult each profile's results for acceptance
against its exact inputs; layout migration alone does not establish verification. Consult the owning profile’s results.md and evidence/summary.json for original-input acceptance; no repository-wide status matrix is maintained.
Existing workspaces that have not migrated retain their version-local instructions.
Managed preparation is opt-in and does not change the Creusot workflows.
Start new crates with the [new-crate procedure](templates/aeneas-managed/README.md).
A blocked [new-version template](templates/aeneas-managed/README.md) makes incomplete setup explicit.

## Entry points and source

Migrated versions have independent Cargo workspaces and thin setup/verify wrappers
around `scripts/aeneas-manage.py`. Common commands are `setup`, `verify`, `doctor`,
`lint` and `check-source`, each taking a version root. `--profile` selects a named
profile; `--offline` requires populated caches. `setup --sources-only` restores just
application source. Regular setup/verify never updates maintained locks.
Use the version's `scripts/setup.sh` and `scripts/verify.sh` for complete workflows:
the setup wrapper can also prepare the profile's locked auxiliary feature graphs.
The native CI workflow uses these same entry points.

Lock updates are explicit reviewed edits following the new-version template: obtain and independently check the new archive/commit, regenerate its full inventory, review the manifest surface, and update tool pins/patches with fresh extraction and evidence. `scripts/migrate-aeneas-layout.py` is a one-time importer for the old captured layout, not a normal setup or lock-update command; its legacy-cache prerequisites are not runtime dependencies of migrated crates.

Schema-1 registry source locks contain canonical crates.io URL, exact name/version,
archive SHA-256, and every expanded file's SHA-256 and executable bit. Git exceptions
contain an HTTPS URL, full commit, optional subdirectory and the same inventory.
Git sources with symlinks/submodules currently fail explicitly. Source lives in the
version's ignored `.work/source`. Archives are checked before expansion; links,
traversal, duplicates and oversized expansion are rejected. Modified sources fail,
rather than being silently repaired. Archive caches are content-addressed.

## Tools and platforms

Each profile pins Aeneas, Charon, Rust, Lean, cargo-proofs and OCaml packages. Ordered
patches have checksums and a resulting Git tree. The `aeneas-opam-v1` recipe checks
`charon-pin`, imports exact opam packages, builds isolated sources, and records host
compiler information and binary hashes. Cache identities and component reuse include
the complete recipe hash, SDK version/path and relevant compiler/build flags. Incomplete caches are never accepted.
Tools live under the repository's ignored `.work/tools`, so a crate does not depend
on another crate's installation. Compatible compiler components are reused only
after their pinned sources and recorded binaries have been rechecked.

Setup normally creates an isolated opam switch. `AENEAS_REUSE_OPAM_SWITCH` explicitly
selects a pre-existing switch read-only after checking the complete package set.
`AENEAS_BOOTSTRAP_ROOT` and `AENEAS_PROOFS_RS_CACHE` can seed Git objects from local
clones; exact revisions and patches are still checked. `AENEAS_LAKE_CACHE` can seed
`.lake/packages` after revision and clean-source checks. None changes the pins.

Linux x86_64 and macOS arm64 are recognized native hosts. Host binaries are not
compared across OSes. Target/features and generated-model equality are checked per
run; portability is not a claim that another target has passed. Models are under
`proofs/Generated/<target>`, selected by a rendered srcDir in an ignored build copy.
Verify does not rewrite their bytes. Lake dependency sources are restored at locked
commits before fingerprints; proof runs disable automatic release-build downloads.

Profiles can prepare locked auxiliary Cargo feature graphs and validate current
source/API inventories through their configured checks. Their native tool identities
are recorded before and after. Historical records are provenance only; a Mac run
does not certify Linux execution.

## Evidence and SARIF

Local runs retain separate native, extraction, Lean and axiom-audit logs, before/after
fingerprints and a terminal result. Fingerprints observe the actual pinned native
and extraction Rust, Cargo, Lean and Lake binary hashes and versions, Rust cfg,
host/target, SDK and compiler context before and after the run. Caller compiler
overrides and disabled Python assertions are rejected rather than silently changing
the locked verification input. Failed steps cannot produce a passed result.
Git keeps compact summaries and archive descriptors; full logs and repeated snapshots
remain in ignored local archives. The [publication guide](publication.md) documents
packing, integrity checks, restore and the explicit compatibility-fixture exceptions.
The active result summary and accepted output bundles are outside the fingerprint;
specifications, scripts, locks and proof sources are inputs.

`proofs-prepare.toml` lets the CLI restore inputs before Cargo discovery and inside
its isolated checkout. Its command is an argv array. The CLI independently checks
archive/Git inventories, replays tool patches, and compares build-copy Lean sources
with maintained sources. Only standard Lake execution and the CLI's own audit
produce formal results; a repository script's success is not proof success.

Preparation stdout/stderr remain local. SARIF retains upstream identities, lock
references, patch hashes, standard tool output and CLI-generated audit code, but
not repository scripts, patch contents, preparation logs or native-test logs.
`--proofs-config` selects a profile report relative to its Cargo package and keeps
recording state separate. Profile preparation settings can be selected by the longest
report-directory prefix in `[profiles."aeneas/profiles/<name>"]`; `@HOST@` in the
prepared Lean path resolves to the supported native target. Existing publication gates
are retained. Source/configuration/tool identities and maintained Lean input digests
are recorded, along with Rust target, selected features and cfg.

## Acceptance

Source tests cover offline restoration, paths with spaces, concurrent initialization,
corruption, missing/extra files, executable bits and unsafe archives. CLI tests cover
independent archive checks, log separation, preparation failure, path containment
and target-specific Lean module discovery. Structural layout lint does not replace actual CLI preparation and report-validation checks for every profile/partition. An uncommitted checkout must reach the existing publication prerequisite, rather than an earlier configuration error. Unit tests do not replace actual target
extraction and Lean verification. Historical evidence remains tied to historical
inputs; no history rewrite or automatic publication is part of migration.

Concurrent setup/verify operations lock all dependent crates in a stable order.
Fingerprints recursively include declared profile dependencies and every configured
auxiliary tool, including ordinary and naming variants.

`AENEAS_TOOL_CACHE` and `AENEAS_ARCHIVE_CACHE` explicitly select absolute shared
cache directories for fresh/isolated checkouts. Existing different caches are never
replaced. Recording forwards the tool cache. Single-crate wrappers can also forward
their archive cache; multi-crate recording preserves each default local cache unless
the caller explicitly selected one shared archive cache at initial setup. Choose
that shared cache before preparing dependent crates when offline isolated-checkout
restoration is needed. All source inventories, tool trees and binary hashes are
still rechecked.

Ordinary setup/verify use guarded, pinned subprocess environments and preserve user home/cache configuration. Sourcing a version’s `scripts/env.sh` is an explicit interactive activation: it selects the locked Rust/Lean versions and version-local build output. The recording wrapper performs that activation inside its child shell; it does not change the caller’s shell environment.

## Native CI entry point

The manual `Managed Aeneas native verification` workflow starts a fresh checkout on
Ubuntu x86_64 and macOS arm64 for one selected crate/profile. It installs host
prerequisites, restores locked tools/source, verifies once, then repeats in offline
mode with the populated dependency cache. The OS labels follow the
[GitHub runner reference](https://docs.github.com/en/actions/reference/runners/github-hosted-runners). It has
read-only repository permission and does not publish SARIF or upload evidence.
This workflow definition is not evidence that a Linux run has passed; target-specific
results are accepted only after the corresponding run completes. Only migrated
workspaces are offered as selectable targets.

## Cache validation upgrades

Shared Git source validation is read-only and compares actual tracked bytes, modes
and symlink targets with the fixed staged blobs. Git optimization flags are not
accepted as evidence that a file is unchanged. Nested Aeneas/Charon repositories
retain their independently checked locks, including intentional patches.

A narrowly reviewed recipe transition may reuse compiler components after checking
all source trees and binary hashes again. `recipe-compatibility.json` binds the exact
previous and current recipe file hashes; all other host/SDK/flags/tool inputs must
match. Its own hash participates in the new cache identity. Old receipts remain
unchanged; the new receipt records the donor receipt hash and reason. Unknown recipe
changes fail closed, and this mechanism does not turn an incomplete or absent store
into an offline-ready cache.

## Reading preserved specifications and older evidence

Independent contracts and historical analyses retain their original content and
scope. A historical `upstream/` or `capture/source/` reference denotes the same
release bytes now restored under `.work/source`; the source lock records their
complete inventory. Historical `proofs/<Model>.lean` references correspond to
`aeneas/profiles/<profile>/proofs/Generated/<target>/<Model>.lean` after fresh
extraction. Authored proof modules retain their names within the profile's `proofs`
directory. Old `.tools` and `/workspace` locations identify historical installations,
not commands to use for current setup. Current commands and paths are in the version
README and thin wrappers. Historical input maps/commit references and accepted input
archives keep these associations explicit without rewriting old evidence.

## Subject units within one profile

A profile may declare `[profiles.<name>.units.<subject>]` entries in
`aeneas/profiles.toml`, each with a version-relative `path` and ordinary explicit
`dependencies`. Its `verification.json` must select `"execution": "all-units"`.
Only the outer name is a public profile. Each subject has the normal pinned inputs,
extraction configuration, theorem/API inventory and separate Lean package. Internal
dependency identities use `<profile>/<subject>`, for example
`crate/version:default/arithmetic`.

Setup prepares the entire graph. Normal verification runs every subject through
the standard native/extraction/Lake/audit pipeline and checks fingerprints before
and after the combined run. Any subject failure prevents combined success. Separate
Lean processes permit conflicting generated auxiliary names; they do not establish
semantic correspondence between independently generated models. `--unit <subject>`
is a focused maintenance operation and never establishes whole-profile acceptance.
Per-subject CLI preparation must select the same unit and build directory; standard
CLI build/audit results remain the only source of SARIF proof success.
