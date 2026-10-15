# Shared tool procedures and evidence formats

Use the [playbook](playbook.md) and [plan template](templates/crate-plan.md) to choose a target.
The two Python standard-library-only tools described here do not define a crate's contracts or
verification target list. Keep the existing httpdate-specific runner and checker as they are.

## Capture release provenance

```bash
python3 scripts/capture-crate-release.py --help
# Set NAME / VERSION / DIRECTORY after choosing the target.
python3 scripts/capture-crate-release.py NAME VERSION --output DIRECTORY
python3 scripts/capture-crate-release.py --check DIRECTORY
```

A normal capture reads the crates.io version API and static.crates.io archive over HTTPS, checks that the checksums match, and saves them to the specified directory. It does not build or run crate code. It refuses to overwrite an existing directory. It rejects absolute archive paths, `..`, duplicate files, and symlinks / hard links, and extracts source bytes without modification. Each download has a 30-second timeout; metadata is limited to 8 MiB, the archive to 128 MiB, and total extracted content to 512 MiB and 100,000 files.

Files saved:

- `manifest.json`: crate / version, retrieval time, URL, checksum, SHA-256 of all source files,
  contents of `.cargo_vcs_info.json` if present, and registry metadata such as license and MSRV.
- `registry-metadata.json`: the exact bytes of the retrieved version API response.
- `release.crate`: the archive whose checksum was verified.
- `source/`: all regular files, including the original Cargo manifest, source, bundled licenses, and VCS metadata.

Capture can also run offline using an already retrieved archive / metadata.
Example using these inputs (the output directory must not exist yet):

```bash
python3 scripts/capture-crate-release.py httpdate 1.0.3 \
  --metadata-file httpdate/1.0.3/verification/correspondence/registry-metadata.json \
  --archive-file /path/to/httpdate-1.0.3.crate \
  --output /tmp/httpdate-release-capture
```

`--check` does not connect to the network. It rechecks the metadata / archive / extracted source inventory and hashes, and rejects added or deleted files. This checks the consistency of the saved record; it does not re-authenticate the current registry or prove equivalence with a Git tree or verification fork. It also handles distributed packages without VCS metadata. In that case, do not guess an unknown source commit.

Record correspondence with Git upstream by comparing archive VCS information, the copied-from commit, and actual source separately. For comparison dependencies, preserve the original Rust bytes and show any build manifest changes, such as a package name change, separately. The existing httpdate [provenance check](../httpdate/1.0.3/scripts/check-upstream-release.py) compares that version's saved reference with two Git commits. Shared capture automates release preservation and consistency only; create API-by-API correspondence maps and finite differential tests within the target crate.

## Audit a saved proof bundle read-only

```bash
source scripts/activate.sh
python3 scripts/audit-proof-evidence.py httpdate/1.0.3 --reconstruct-root-goals
```

The default manifest is `VERSION_DIRECTORY/verification/evidence/latest/manifest.json`.
Use `--manifest PATH` to specify another bundle. Coma/why3find formats were checked in the current
Creusot 0.13 environment; this does not claim automatic interpretation of other verifiers or future formats.

Required common manifest fields:

| Field | Meaning |
| --- | --- |
| `cache` | Explicitly `false`. This is a condition of the recorded run; the audit does not create a fresh run. |
| `inputs_sha256` | Input/tool hash map keyed by paths relative to the version directory or by absolute paths. |
| `targets` | Selected target name → session information. Must be nonempty; zero goals are not allowed. |
| `expected_open` | Target name → session information and a nonempty `reason`. It must actually be open. |
| `excluded_generated` | Target name → reason for exclusion. The three classifications must not overlap. |
| `total_session_goals` | Total number of selected closed root goals only. |
| `generated_target_count` | Total number of targets in the three classifications above. |

Each session record has `goals`, `goal_inventory`, `open_goals`, `proof_json_sha256`,
and `coma_sha256`. In the bundle, files are `<target-name>/proof.json` and `<target-name>/target.coma`.
If there are expected-open goals, save Why3find's normal unresolved exit value `1` in `open-prove.exit`.
The concrete [httpdate manifest](../httpdate/1.0.3/verification/evidence/latest/manifest.json)
is an example of this format.

The audit checks current input hashes, the saved target inventory, Coma/session hashes, unique root lists,
presence of target VCs, nonempty proof trees, closed/open classifications and totals, and expected-open exit status.
It also rejects unrecorded source added under `crate/src/**/*.rs`. For a different layout, use
`--source-root DIRECTORY`; repeat it if needed to cover multiple source trees. After the checks, it
rechecks input/session hashes and does not modify the manifest or evidence.

`--reconstruct-root-goals` independently enumerates every root in each Coma using Why3 and checks for an exact match with the session. Without this, it cannot detect a consistent omission of the same helper goal from both the manifest and session. Configuration is read from `XDG_DATA_HOME` after activation; in another environment, specify `--why3-config PATH` and `--why3-library DIRECTORY`.

If excluded generated Coma files are not saved in the bundle, manifest totals alone cannot independently check the full generated inventory. Pass the complete Coma root from a fresh run with `--generated-dir DIRECTORY` to check for added, missing, and unclassified targets as well. Each version's fresh runner is responsible for checking the complete inventory before saving.

This audit does not rerun SMT proofs or recheck certificates. It does not cryptographically authenticate the string in the `prover` field. It does not assess API / feature scope, contract semantics, or completeness of unrecorded non-Rust inputs and dependency code. The crate-local runner is responsible for collecting fingerprints for required source/specification/assumption/configuration/script/tool inputs. This is not a replacement for a fresh proof of a new crate, corruption guards, or trust review.

## Check the tools

```bash
source scripts/activate.sh
python3 -m unittest discover -s scripts/tests -v
```

The tests corrupt synthetic captures / sessions in temporary directories and check read-only operation
and rejection of changed inputs, added source, missing goals, empty proof trees, conflicting
classifications, abnormal exits, and invalid archive paths. The independent Why3 enumeration test is
skipped when the tool is unavailable; run it after activation as above. Synthetic sessions do not count
as actual proof results. The audit result using the actual httpdate bundle is saved separately in the
[shared tools validation record](common-tools-validation.json).
