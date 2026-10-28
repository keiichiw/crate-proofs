# Add a crate version with Aeneas and Lean

This is the entry point for a **new** `<crate>/<version>` workspace. Read the
repository Aeneas skill for proof discipline and the [management guide](../../aeneas-management.md)
for runtime/cache behavior. Start from a small useful core, not a whole-crate claim.
The template remains blocked until its crate-specific inputs have been reviewed.
There is no automatic new-crate or tool-lock initializer.

## 1. Choose source and scope

Choose an exact published version, native target and Cargo features. Inventory
public APIs, dependencies, build scripts, unsafe code and generic/IO boundaries.
Write down selected, unproved and excluded APIs, explicit preconditions and trusted
standard-library models. Begin with `default`; use named profiles only for distinct
proof/tool/feature selections or proof dependencies. Profiles are not success labels.
Linux x86_64 and macOS arm64 need separate generated models and acceptance results.

## 2. Create the workspace and pin source

Run from the repository root. Replace both placeholders with reviewed real values;
these commands do not select a crate or version for you. Use a new empty destination.

```bash
CRATE_NAME='<actual-crate-name>'
CRATE_VERSION='<actual-release-version>'
VERSION_ROOT="$PWD/$CRATE_NAME/$CRATE_VERSION"
mkdir -p "$VERSION_ROOT"
cp -R verification/templates/aeneas-managed/scripts "$VERSION_ROOT/"
cp -R verification/templates/aeneas-managed/aeneas "$VERSION_ROOT/"
python3 scripts/capture-crate-release.py "$CRATE_NAME" "$CRATE_VERSION" \
  --output "$VERSION_ROOT/.work/release-capture"
python3 scripts/capture-crate-release.py --check "$VERSION_ROOT/.work/release-capture"
python3 - "$VERSION_ROOT" <<'SOURCE_LOCK'
import json, shutil, sys
from pathlib import Path
sys.path.insert(0, str(Path.cwd() / 'scripts'))
from aeneas_management import source
root = Path(sys.argv[1]); capture = root / '.work/release-capture'
manifest = json.loads((capture / 'manifest.json').read_text())
lock = {'schema_version': 1, 'kind': 'registry',
        'name': manifest['crate']['name'], 'version': manifest['crate']['version'],
        'url': manifest['archive_url'], 'sha256': manifest['archive_sha256'],
        'files': source.inventory(capture / 'source'), 'aliases': [],
        'manifest_exceptions': {}}
source.validate_lock(lock)
source.check(capture / 'source', lock)
with (root / 'source.lock.json').open('x') as out:
    out.write(json.dumps(lock, indent=2, sort_keys=True) + '\n')
cache = root / '.work/cache'; cache.mkdir(parents=True, exist_ok=True)
shutil.copyfile(capture / 'release.crate', cache / (lock['sha256'] + '.crate'))
source.restore(root, offline=True)
SOURCE_LOCK
python3 scripts/aeneas-manage.py check-source "$VERSION_ROOT"
```

Capture checks the archive against registry metadata; independently review that
metadata and the release's VCS identity. For an offline capture, supply both
`--metadata-file RESPONSE` and `--archive-file ARCHIVE` to the capture command.
Full-commit HTTPS Git acquisition is reserved for unreleased versions; its lock
uses `kind=git`, `url`, full `commit`, optional `subdirectory`, and the same file
inventory. Do not substitute a submodule or copy upstream source into Git.

Create an independent Cargo workspace from the release manifest. Point library,
tests, benches and build-script paths into `.work/source`, preserving dependencies
and features. Generate/review Cargo.lock explicitly. Document every deliberate
verification-only omission in `manifest_exceptions`; do not silently remove build
scripts or difficult feature paths. Add version-local AGENTS.md with proof scope
and review responsibilities. Source restoration alone does not establish this
manifest correspondence. Once Cargo.toml exists, run the manifest/source checks:

```bash
python3 scripts/aeneas-manage.py setup "$VERSION_ROOT" --sources-only --offline
```

Unlike source.restore, setup --sources-only also requires and checks the outer Cargo manifest.

## 3. Pin compatible tools and patches

Use the following minimum schema to create a reviewed target-specific tool lock.
A migrated target's lock can illustrate the complete schema, but its versions and
models are not defaults for another crate:

```json
{
  "schema_version": 1,
  "recipe": "aeneas-opam-v1",
  "native_rust": "<reviewed Rust channel>",
  "extraction_rust": "<Charon-compatible Rust channel>",
  "lean": "<backend-compatible Lean toolchain>",
  "opam_sha256": "<SHA-256 of opam.locked>",
  "repositories": {
    "aeneas": {"url": "<HTTPS URL>", "revision": "<full commit>", "tree": "<resulting Git tree>", "patches": []},
    "charon": {"url": "<HTTPS URL>", "revision": "<full commit>", "tree": "<resulting Git tree>", "patches": []},
    "proofs-rs": {"url": "<HTTPS URL>", "revision": "<full commit>", "tree": "<resulting Git tree>", "patches": []}
  }
}
```

Replace every placeholder before setup. Confirm Aeneas's `charon-pin`, Charon's
Rust channel and the Lean backend's toolchain. Export the exact OCaml package set
to opam.locked. Every patch entry has `file`, `sha256`, `purpose`, `regressions`;
its order and resulting repository tree are fixed. Distinguish extractor fixes,
Lean emission fixes and trusted standard-library models. An empty patch list does
not supply the managed CLI preparation extension: review and pin the required CLI
capability. Declare additional tool variants through `auxiliary_tools` only when
needed. Setup checks the lock; it does not generate or update it.

```bash
bash "$VERSION_ROOT/scripts/setup.sh"
```

## 4. Extract actual bodies and write proofs

Specify roots, selected dependency bodies, expected output names and required
Lean definitions in `extraction.json`. Wire each extraction and its maintained
`proofs/Generated/@TARGET@/` destination into `verification.json`. The
[extractor reference](../../../.agents/skills/aeneas-lean-verification/references/setup-and-runner.md)
describes the supported selectors and rejection checks.

Run exploratory extraction into a new `.work/` directory using the pinned tool
environment prepared for this profile. Inspect complete output and source spans
before promoting real generated bytes; never edit generated Lean. Write independent
mathematical specifications, then prove actual bodies with total-success contracts.
Keep authored Specs/Proofs separate from Generated. Pin lean-toolchain and Lake
manifest; use `@AENEAS_BACKEND@` and `Generated/@TARGET@` in lakefile.toml.

Record actual theorem names/modules/preconditions in `theorems.json` and API
mappings in `proofs.toml`. Include unproved/excluded APIs in the coverage ledger.
Register required boundary/regression checks through additional_checks/post_checks,
and every profile/crate dependency in profiles.toml. Do not weaken a domain or
replace reachable application behavior merely to obtain a passing extraction.

## 5. Check configuration, verify and save results

Remove migration_blockers only after all required inputs and checks are faithfully
configured. Structural lint is not proof acceptance.

```bash
python3 scripts/aeneas-manage.py lint "$VERSION_ROOT"
bash "$VERSION_ROOT/scripts/verify.sh"
bash "$VERSION_ROOT/scripts/verify.sh" --offline
```

The full runner records native tests, exact regeneration comparisons, standard
Lake build, theorem/transitive axiom audit and before/after fingerprints separately.
Only propext, Classical.choice and Quot.sound are allowed audit dependencies.
A successful native test or setup command is not a proof. Offline verification
requires previously prepared tools, sources and dependency graphs.

Keep complete runs under ignored `.work/`. Use the [publication guide](../../publication.md)
to archive a run, verify/restore it and create a compact summary. Commit only
reviewed summaries/descriptors and explicit test fixtures, not raw execution logs
or repeated snapshots. A local-only archive is not downloadable from a fresh clone.
Update results with exact scope, target/features, limitations and original input
identity; an older success does not certify later edits.

## 6. Check CLI preparation separately

Local proof verification requires no push. The optional record wrapper invokes
standard Lake and the CLI audit; it is separate from setup/verify and retains the
CLI's source-publication prerequisites. Neither a preparation script nor an
uncommitted-source rejection is a successful proof recording. Upload/publication
requires separate explicit authorization.

CLI wiring is a separate acceptance check from layout lint. Set each report’s `[tool].lean_dir` to `.work/selected-proofs` (or the exact prepared build path), not the former `proofs` source directory. Every nested preparation profile table requires its own `schema_version = 1`. Exercise every report partition through the pinned CLI; on an uncommitted checkout it must reach the existing commit/push prerequisite rather than fail parsing, path resolution, tool checks or API/theorem validation. Each API mapping in a report needs a unique theorem name; use exact specialized theorems when a generic proof covers multiple concrete API instances. Never drop mappings to satisfy that constraint.

Use the official 40-character base commit for `[tool].version`; describe applied patches in the tool lock. CLI proof entries currently accept only `api`, `module`, `theorem` and `precondition`. Keep additional classification metadata in the complete catalog and specifications, explicitly list any omitted descriptive fields in the partition manifest, and compare the exact supported-field projection with the ordered union of report partitions. Preconditions and API coverage must never be dropped by that projection.

Record bugs and unsupported boundaries using the [finding template](../finding.md)
and [storage policy](../../findings.md), with pinned reproduction inputs and
explicit native/formal evidence limits.
