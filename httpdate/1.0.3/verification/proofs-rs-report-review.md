# httpdate submission preparation

The English report and actual cargo-proofs configuration now live in
[crate/proofs.toml](../crate/proofs.toml), next to the package manifest. The separate
editorial draft was consolidated into that file. The report follows the supplied
[write-proofs-report skill](https://raw.githubusercontent.com/proofs-rs/proofs-rs/main/skills/write-proofs-report/SKILL.md).

The report is prepared for publication using an upstream cargo-proofs revision
containing the API-name resolution fix. Submit that fix upstream first, then pin
the fixed upstream revision and update the provisional setup and recorder checks
before producing the final SARIF. The local patched recorder described below is
preparation tooling; its patch explanation is omitted from the public report on
that basis. The fixed upstream revision has not yet been selected here.

## Scope and evidence

The first report selects exactly these four API bodies:

| Public API | Generated target |
| --- | --- |
| `httpdate::parse_http_date` | `parse_http_date` |
| `httpdate::fmt_http_date` | `fmt_http_date` |
| `<httpdate::HttpDate as std::str::FromStr>::from_str` | `date/impl_FromStr_for_HttpDate/from_str` |
| `<httpdate::HttpDate as std::fmt::Display>::fmt` | `date/impl_Display_for_HttpDate/fmt` |

`target = "annotated"` makes APIs eligible for discovery; it does not limit discovery
to these four. The recording command selects four exact Coma paths, and the wrapper
rejects SARIF whose contract set differs from the table. Other public traits,
including the open unconditional `From<SystemTime>` refinement, are excluded from
this submission. Its bounded helper body remains supporting evidence.

Supporting helper proofs are the separate, immutable
[full-suite manifest](evidence/httpdate-run-Nh8aCaki/manifest.json) and
[independent audit](evidence/httpdate-run-Nh8aCaki/independent-audit.json), recorded
with source snapshot `9e9100c8b1727568d60a9db388f352eb4a8bf040`. They cover 64 selected
targets and 268 closed root goals, including extra APIs outside this report.
The [native comparison](correspondence/evidence/correspondence-qZmQ5PXk/manifest.json)
is separately bound to that manifest. It establishes finite observed agreement,
not formal equivalence with the release. See the [specification](specification.md),
[assumptions](stdlib-assumptions.md), and [source correspondence](correspondence/README.md).

The wrapper audits this supporting archive and unchanged source/configuration
fingerprints before either local verification or recording. Fresh four-API proofs
do not replace the helper archive or promote the full suite's latest pointer.
On another machine, the strict archive audit requires its recorded tool files too;
it is not a portable re-proving command. To change source or tool identities,
regenerate the full suite first, then review and update the supporting manifest pin
in the submission wrapper and report. Do not rewrite the historical manifest.

## Isolated recorder

The original environment's cargo-proofs 0.3.4 remains unchanged because existing
formal evidence fingerprints that binary. It emits proofs schema version 1;
the [current CLI specification](https://github.com/proofs-rs/proofs-rs/blob/d25301d5ef2e57409f46db9ef775be1550037b42/cli/README.md)
requires version 2 and its dependency snapshot for publication.

The current local preflight tooling uses cargo-proofs 0.3.5 at commit
`d25301d5ef2e57409f46db9ef775be1550037b42`, with the narrow
[external-trait name patch](recorder/cargo-proofs-0.3.5-external-traits.patch).
The unmodified scanner produces `date::std::fmt::Display` and
`date::std::str::FromStr` for these methods. The patch reuses its existing external
path renderer, removing the spurious private-module prefix while preserving
external qualification and local trait identities. It adds two regression tests.
It does not alter Creusot, the prover, contracts, safety checks, proof sessions,
Git provenance checks, or SARIF success criteria. Service catalogue matching is
still authoritative; a local name check is not server acceptance.

Source archive and patch hashes are fixed in [pin.json](recorder/pin.json). Setup
runs the recorder's test suite, installs under the ignored
`.local-verification/submission-tools/httpdate/`, and saves an installation manifest
with the binary hash and test log path. The recording wrapper verifies that manifest
and invokes the binary explicitly, without replacing the archival tool on `PATH`.

From the repository root, with the documented verification environment installed:

```bash
source scripts/activate.sh
python3 httpdate/1.0.3/scripts/setup-submission-recorder.py
python3 httpdate/1.0.3/scripts/proofs-submission.py local
```

Python 3.11+, curl, tar, and patch are needed in addition to the pinned toolchain.
Setup downloads public source and Cargo dependencies. It does not log in or publish.
The `local` mode audits the supporting bundle, creates a fresh build/output directory,
runs Alt-Ergo/Z3 with caching disabled, reconstructs every selected root goal, and
checks declaration spans against the actual source. Diagnostics and input hashes
are retained under `verif/submission-*/`; `checked.json` is explicitly a local
preflight result, not a SARIF recording. Native tests are separate from this run.

## Record after the source is public

First replace the provisional patched recorder with the fixed upstream revision
as described above. The commands below describe the recording workflow after that
update; the current setup and wrapper still pin the local patched build.

Commit the reviewed submission files and push that commit to the GitHub `origin`
before recording. These are separate user-authorized actions. cargo-proofs itself
requires a clean working tree, fetches the remote, and verifies remote reachability.
The configured remote alone does not establish public accessibility; confirm the
source and immutable evidence URLs without authentication.

```bash
source scripts/activate.sh
python3 httpdate/1.0.3/scripts/proofs-submission.py record
```

The wrapper runs the real `cargo proofs run -- cargo creusot ...` workflow in its
detached temporary checkout. It retains `--span-mode absolute` and fresh proof
sessions, then checks the saved SARIF for four exact API identities, passing results,
source locations, the expected crate/tool, and proofs schema version 2. It neither
constructs nor rewrites SARIF. The recorder validates locked Cargo metadata and
rejects tracked-input changes. Its current parser rejects a nested `--`, so the
Creusot command does not add the usual `-- --locked` suffix; the wrapper also checks
`cargo metadata --locked` beforehand.

To recheck an actual recorded file:

```bash
python3 httpdate/1.0.3/scripts/proofs-submission.py check-sarif --sarif /path/to/run.sarif.json
```

Review that file's source commit, dependencies, conditions, and logs before any
publication. The Creusot importer registers `panic_contract`; functional
postconditions in the prose are supported by the proof archive, not a separately
registered functional-correctness or `no_ub` property.

Login, `publish --dry-run`, and publication remain separate steps requiring explicit
authorization. Even dry-run authenticates and may request server-side catalogue
import. Confirm Creusot 0.13.0 is selectable and each API maps uniquely to the
service catalogue. Unauthenticated catalogue reads during preparation returned
404, so server-side matching has not been established. No SARIF recording or
publication has been performed during this preparation.
