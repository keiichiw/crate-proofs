# Verified Rust crates for proofs.rs

This repository prepares independently verified Rust crate forks, contracts, reproducible evidence, and scope documentation for eventual submission to proofs.rs. Submission and publication are separate from local verification. Place each target under `<crate>/<version>/`, with its crate source, Cargo workspace, verification scripts, specifications, and results. Keep Cargo workspaces and lockfiles separate by version so multiple versions of the same package can be added. Do not add a Cargo workspace at the repository root.

## Native tests and differential comparisons

Use ordinary Rust/Cargo on PATH, a native linker, Bash, and Python 3. The repository selects Rust 1.91.0 through `rust-toolchain.toml`; Rustup installs it if necessary. No formal verification environment activation is needed:

```bash
bash form_urlencoded/1.2.2/scripts/run-differential.sh
bash percent-encoding/2.3.2/verification/differential/run-full-scope.sh
bash httpdate/1.0.3/scripts/check-correspondence.sh
```

The runners preserve the caller's `CARGO_HOME` and `RUSTUP_HOME`, use locked dependencies, and may download missing packages. Set `CARGO_NET_OFFLINE=true` to require an existing cache. The first two commands include native tests and feature checks; httpdate's standalone native tests can be run with `cargo test --locked --release --manifest-path httpdate/1.0.3/Cargo.toml`. Native results are separate from formal evidence. Dedicated formal setup and activation below are only needed for proof workflows.

## Local macOS arm64 tools

For a native Apple Silicon tool installation, use the [local setup guide](verification/local-macos.md). It installs pinned tools separately from the existing user Creusot installation and checks a fresh sample proof. The runners now select the local toolchain on macOS; the httpdate platform review is linked from that guide. See each version’s results for actual crate evidence.

## Shared tool environment

The recorded cloud setup uses Linux x86_64; native macOS arm64 is also available through the [local setup guide](verification/local-macos.md). For the cloud setup, prepare the three repositories and commits recorded in `verification/toolchain-repositories.json` under `/workspace`. Rust 1.91.0, Creusot 0.13.0, nightly-2026-06-22, cargo-proofs 0.3.4, and the Why3 / Why3find / prover pins are recorded in the root `scripts/` and `verification/toolchain-opam.export`. The shared Why3find configuration is the root `why3find.json`. Each version's `why3find.json` refers to it.

To set up the environment from scratch:

```bash
bash scripts/setup-cloud.sh
source scripts/activate.sh
bash scripts/check-tools.sh
```

If setup is already complete, run activate and check. Check verifies an independent bootstrap sample proof; it does not check the results for individual crates. Environment packages and tool data are stored in `/workspace/.cargo`, `/workspace/.rustup`, `/workspace/.opam`, and `/workspace/.local`.

## Aeneas + Lean workflow

For new Aeneas targets, start with the [managed new-crate procedure](verification/templates/aeneas-managed/README.md) and the [Aeneas/Lean skill](.agents/skills/aeneas-lean-verification/SKILL.md).
The [management guide](verification/aeneas-management.md) describes checksum-pinned
source restoration, isolated tool caches, profile-specific proofs and setup/verify
entry points. Existing targets retain their own instructions until migrated.

Shared helpers include `scripts/aeneas-manage.py` for managed setup/verification,
`scripts/aeneas-extract.py` for selected-body extraction, and `scripts/aeneas-audit.py`
for named-theorem and transitive-axiom audits. These do not establish automatic
whole-crate verification or proofs.rs recording. Read each target's contracts,
results and trust boundaries; native tests remain separate from formal proof.
The [evidence guide](verification/publication.md) explains local archives and
current-input versus historical acceptance.

## Work by crate

Follow the commands and verification scope documented in each version's README, AGENTS.md, and skill. Specify that version's `Cargo.toml` for ordinary Cargo commands, and use its `scripts/verify.sh` for formal verification. Place additional crates and versions in the same layout.

Start investigations of a new crate with the [playbook](verification/playbook.md) and
[plan template](verification/templates/crate-plan.md).
The [shared skill](.agents/skills/creusot-verification/SKILL.md) collects practices from httpdate for type boundaries, failure contracts,
trait refinement, external models, diagnostics, and correspondence comparison.
The [shared tools](verification/tools.md) handle release provenance capture and read-only audits of saved proof bundles.
Contracts, API/features selection, fresh proof runners, and differential comparison corpora are defined per crate/version.
Do not treat hyper or atoi as verified; first assess feasibility on an important pure core.

| Crate | Version | Procedure and scope |
| --- | --- | --- |
| adler2 | 2.0.1 | [Aeneas/Lean harness](adler2/2.0.1/README.md) / [results](adler2/2.0.1/verification/results.md) |
| ipnet | 2.12.2 | [Aeneas/Lean harness](ipnet/2.12.2/README.md) / [scope and results](ipnet/2.12.2/aeneas/profiles/default/results.md) / [findings](ipnet/2.12.2/verification/findings/README.md) |
| httpdate | 1.0.3 | [Procedure](httpdate/1.0.3/README.md) / [scope and recorded results](httpdate/1.0.3/verification/coverage.md) |
| form_urlencoded | 1.2.2 | [Scope](form_urlencoded/1.2.2/verification/coverage.md) / [recorded results](form_urlencoded/1.2.2/verification/results.md) |
| percent-encoding | 2.3.2 | [Scope](percent-encoding/2.3.2/verification/coverage.md) / [recorded results](percent-encoding/2.3.2/verification/results.md) |

Use the linked results pages and manifests for each version’s current input freshness and selected proof scope. Historical bundles remain tied to their own frozen inputs. These are not whole-crate or unmodified-release verification claims. Native and differential tests are reported separately.

For form_urlencoded's expanded scope, run `bash form_urlencoded/1.2.2/scripts/verify.sh` for standard Why3find verification; see its results page for the current `verification/evidence/latest` bundle. The historical direct-SMT evidence remains under `latest-direct`. For percent-encoding, the independent Cargo workspace and lockfile are inside `crate/`; use `scripts/verify-why3find.sh` for fresh native checks followed by standard verification. Its results page records the standard run status and evidence.

A refresh must prove form_urlencoded first, then review and update percent-encoding's pinned dependency evidence path and SHA-256 before its native and formal runs. See the [refresh procedure](verification/refresh.md).

A draft configuration for the Codex cloud environment has been saved. Publishing and checking restoration in a new task remain separate steps. Review source changes under each version's Git control. Only log in to proofs.rs, push, or publish evidence with explicit authorization.

The maintained English translations change fingerprints recorded by historical proof bundles. See the [language change record](verification/language-change.md) for how those bundles should be interpreted.

## Reports and findings

Use the [report-writing skill](.agents/skills/proofs-report-writing/SKILL.md) for
reader-facing reports and Rust-only finding reproductions. The [finding policy](verification/findings.md)
and [record template](verification/templates/finding.md) describe crate-local
investigation records. Drafting does not authorize publication or upstream posting.
