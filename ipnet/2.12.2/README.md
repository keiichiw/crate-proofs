# ipnet 2.12.2 — Aeneas / Lean

This independent Cargo workspace verifies selected actual bodies from the unchanged
ipnet 2.12.2 release. The official sparse registry index resolved this as the latest
non-yanked stable release on 2026-10-16. The archive checksum and its embedded Git
commit are checked against the pinned upstream submodule. This is not a whole-crate
verification claim.

The Astra agent independently defined [the specification](verification/specification.md).
The Sol agent authors implementation proofs and may consult Astra as an oracle.
The exact accepted scope and evidence are in [results](verification/results.md),
[the theorem inventory](verification/theorems.json), and [API mappings](proofs.toml).

## Reproduce locally

From the repository root, in Bash:

```bash
bash ipnet/2.12.2/scripts/setup.sh  # installs the pinned tools; requires network
bash ipnet/2.12.2/scripts/verify.sh
```

If the dedicated tools and Lake dependencies already exist, only `verify.sh` is
needed. Tool pins and binary identities are in `verification/toolchain.json`.
A fresh independently rebuilt tool binary may differ byte-for-byte; review and
explicitly update its recorded hash before accepting evidence from that installation.
Do not silently upgrade the revisions or lockfiles. No Creusot environment is used.

The verifier checks source and tool identity, regenerates all configured Lean models
through the shared extractor, compares them byte-for-byte, runs native tests separately,
cleans the local Lake package, rebuilds and audits the named theorems, and checks that
input fingerprints stayed unchanged. The audit permits only `propext`,
`Classical.choice`, and `Quot.sound` transitively. Evidence runs are local, ignored,
and preserved under `verification/runs/`.

The containment extension registers concrete fixed-length octet representations
and comparison models for IPv4/IPv6 addresses. Their Rust correspondence is
reviewed and trusted, as detailed in the [model ledger](verification/model-boundaries.md);
an axiom-free Lean proof does not establish that correspondence. Generated Lean
is never edited. Rust-to-LLBC-to-Lean translation, selected Aeneas library models,
and the Lean kernel remain trust boundaries.
Native tests are finite observations, not formal contracts. No login, push,
recording, or publication is performed by the verifier.

## Set-oriented continuation and findings

The [expert review](verification/expert-review.txt) motivates the independent
[CIDR set contracts](verification/set-operations-specification.md): exact
containment, subnet partition, range state preservation and aggregation union
preservation. Mathematical helper theorems are audited separately from contracts
about actual extracted APIs; extraction alone never adds verified coverage.
`tests/cidr_semantics.rs` supplies six independent finite regression suites, also
separate from universal proofs.

The toolchain now includes two reviewed compatibility patches in addition to the
proofs-rs identifier patch: narrow true-valued Charon UB-check lowering/panic
recognition, checked Lean shift-name wrappers, and removal of the unused Debug
argument in the unwrap model registration. The containment continuation adds
only concrete address-type and comparator registrations, with exact modeled
symbols selected in extraction configuration. Their exact diffs are checked
in the dedicated tools and the actual Lake dependency. See
[extraction notes](verification/extraction-notes.md) for scope, Miri configuration,
rejected probes, and remaining Contains comparison boundaries. Upstream ipnet remains unchanged;
generated Lean is only regenerated through the pinned extractor.

[Findings for future upstream PRs](verification/bugs/README.md) include an
end-to-end reproduction of the schema rejecting valid serialized IPv4 networks
in both schema integrations. They contain pinned standalone reproduction code,
generated schemas, validator results and a failing future regression mode. No
upstream issue or PR has been published.

The [second expert response](verification/expert-contains-review.txt) guides
containment followed by range transitions. The six built-in contains
specializations connect through the actual public generic wrappers. The [frozen containment specification](verification/contains-specification.md)
includes every valid prefix, noncanonical addresses, and cross-family rejection.
Comparison/endian connection tests are in `tests/comparison_boundaries.rs`.
The accepted run and ledger determine completion; these plans and finite tests
do not add formal coverage by themselves.

The [range-next specification](verification/range-next-specification.md) covers
`Ipv4AddrRange::next` for all raw endpoints, connecting both returned value and
updated state to a Nat half-open interval. Its scope includes zero/MAX singletons,
reversed endpoints and the full IPv4 range. Existing `mem::replace` and saturating
scalar models remain explicit baseline trust boundaries. The backend adds only
a kernel-proved value lemma about unchanged U32 saturating addition for this
extension. Native state-transition examples are in `tests/range_next.rs`; the
accepted result and audited theorem inventory determine formal completion.

The [IPv4 expansion specification](verification/ipv4-api-specification.md) covers
remaining custom IPv4 range methods, network parent/host/subnet initialization,
public saturating and bitwise overloads, and mask conversion. See the
[IPv4 coverage ledger](verification/ipv4-coverage.md) for API-level distinctions.
Usize-sensitive range contracts explicitly assume `System.Platform.numBits = 64`;
they include the full IPv4 range and every Usize skip index on that target.
A reviewed Result::ok match model is used only for the drop-free
Ipv4Net/PrefixLenError path; Result::map remains extracted. This additional
Rust/model boundary and reused leading-zero/scalar models are recorded in the
model ledger. Only accepted results and audited mappings establish completion.
