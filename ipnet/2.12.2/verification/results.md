# Local verification results — ipnet 2.12.2

Accepted fresh run: **2026-10-16**, [check-ijyIhpBm](evidence/latest/result.json).
The complete verifier passed with **625 audited theorem identities: 160 public
contracts and 465 helpers**. All previous 588 identities are retained. There
are 18 additional public mappings; the three existing new_assert mappings are
strengthened to full runtime domains, with their earlier valid-only theorems
retained as helpers. Contract counts include family specializations, not just
distinct Rust method names. Astra independently specified/reviewed the work;
Sol proved actual extracted bodies; the primary reviewed scope, mappings,
tool changes and the complete evidence.

## Newly accepted public contracts

- Tagged mask conversion and IpNet::with_netmask: complete contiguous-mask
  success/error classification for every bit pattern and both mask tags.
  Mixed families are permitted exactly when the parsed prefix fits the address
  family. Success preserves the original address, host bits and family.
- Clone, eq, cmp and partial_cmp for IpNet, IpAddrRange and IpSubnets (12
  contracts): all raw payloads, V4 before V6, independent numeric stored-field
  keys, exact clone, and Some of the full ordering. Reversed ranges, invalid
  stored prefixes and noncanonical host bits are included. Structural equality
  is not set equality.
- Ipv4Net/Ipv6Net/IpNet::new_assert: exact original fields/tag on valid prefixes;
  invalid prefixes fail assertionFailure in the extracted runtime model.
  This corresponds to the Rust assertion path, distinct from unwrap panic;
  it does not prove const diagnostics, message text or unwind/abort equivalence.
- PrefixLenError and AddrParseError Clone/eq (four contracts): actual singleton
  value operations. These do not imply parser or formatting correctness.

See [independent remaining specification](remaining-tagged-specification.md)
and [coverage ledger](ipv6-coverage.md).

## Minimum number of subnet outputs

For both IPv4 and IPv6, the actual finite iterator trace now has a globally
minimum output count. Against ANY finite list of canonical CIDRs with prefixes
at least the requested minimum and exactly the same address union, the actual
output list has no more elements. Competitors may be unordered, overlapping
or duplicated; they are not assumed to form a partition.

SubnetMinimumMath proves aligned blocks cannot cross a greedy boundary and
uses filtered-cover induction for the length lower bound. SubnetMinimumActual
connects the result to actual next calls, including terminal None, using the
previously proved unconditional trace existence. All raw endpoint pairs with
valid minimum prefix are covered, including empty/full ranges. Cardinalities
are Nat values with no Usize-fit premise. This is a semantic/trace law counted
as helpers, not extra public APIs or a Vec allocation/collect guarantee.

The [previous report](results-ipv6-iteration.md) records retained range,
subnet partition/indexed enumeration, arithmetic, containment and numeric APIs.
All prior 588 theorem names remain audited, including the old constructor laws.

## Tool changes and trusted boundaries

The pinned upstream ipnet release and implementation are unchanged. A small
Lean-only Aeneas binder allocator correction alpha-renames locals that would
shadow ordinary dotted declaration roots, resolving the tagged mask namespace
collision. It changes names, not application semantics; universal hygiene for
all strict-name sets/backends is not asserted.

The unchanged BuiltinClone definition gains @[expose], and its Unit clone
equation is proved by rfl for the actual AddrParseError clone composition.
Bodies and registrations are unchanged; this is not a new generic Rust Clone
correspondence proof. The exact cumulative patch and executable hashes are
pinned. Earlier probe patch bytes are preserved with their evidence.

Existing reviewed standard-library address/layout, comparison, bit-count,
scalar and array/slice correspondences remain trusted, as does the translation
pipeline. No application body is replaced with a desired specification, and
no new Hasher, Formatter or collection model is admitted. See the
[model ledger](model-boundaries.md) and [extraction notes](extraction-notes.md).

## Remaining limitations and findings

**This is not whole-crate or whole-IPv6 verification.** Remaining implementation
obligations include all three aggregate APIs, FromStr parsing, Display/Debug,
Hash, optional serde/schemars bodies, and unselected inherited/default consumers.
Existing network contracts other than explicitly broadened constructors retain
their stated valid-prefix domains; arbitrary invalid raw network behavior is
not silently covered.

Direct probes for BOTH concrete aggregate bodies reach actual Vec::extend and
extend_desugared loops, then fail clean extraction on unresolved capacity,
reserve, as_mut_ptr, set_len and raw-pointer write/add semantics. The subnet
trace does not prove these vector updates. Exact configurations, rejected text,
logs and tool/file hashes are saved in the
[aggregate boundary record](blockers/aggregate-extend/README.md).
Sorting, last_mut backward updates and initial collect also remain separate
obligations. The [parser callback blocker](blockers/ipv4-parser-callback/README.md)
requires preservation of mutable callback state. Existing Formatter/Hasher
boundaries are unaffected by the naming fix; no success claim is made for them.

No new distinct ipnet bug was found. The existing IPNET-003 heapless cfg defect
was directly reproduced for IPv6 as well: the same 43-byte output causes four
allocations/reallocations with heapless-only and zero with the legacy feature.
The nonallocating sink and exact output are checked. This is native evidence,
not a formal serialization proof; see the
[IPv6 reproduction](bugs/heapless-feature-repro/ipv6-evidence.json) and
[existing bug records](bugs/README.md). Original IPv4 evidence remains preserved.
No upstream source edit, issue, PR, push, evidence upload or publication occurred.

## Reproducible evidence

- Pinned source/release/Gitlink/build surface, exact tool source patches,
  reviewed standard sources and executable hashes passed.
- Fresh extraction byte-matched every maintained generated model.
- Clean Lake build, all 625 theorem/mapping/transitive axiom checks and eight
  kernel shift checks passed. Only propext, Classical.choice and Quot.sound
  are allowed; no sorry, custom or native-decision axiom is accepted.
- Native default and no-default-features each passed 33 unit +23 integration
  +56 doc tests (112 each), separately from formal proof.
- The same fresh full run also passed offline/locked all-features native tests:
  37 unit +23 integration +56 doc tests (116). This does not close
  optional-feature proofs or negate the recorded schema/heapless counterexamples.
  The [all-features log](evidence/latest/native-all-features.log) is saved.
- Before/after inputs match. The primary independently verified every artifact
  hash, the current input fingerprint, all 588 prior identities, uniqueness,
  mapping modules/preconditions and zero selected-but-unproved entries.

Run `bash ipnet/2.12.2/scripts/verify.sh` from repository root. The ignored
working directory supplied the accepted run; its selected logs are saved in
[evidence/latest](evidence/latest/package.json). The standalone
`python3 scripts/check-packaged-evidence.py` check passed for 84 saved files,
625 audited theorem identities, 160 public mappings and the current input
fingerprint. It explicitly excludes 3,574 hashed working artifacts, including
the LLBC, rather than presenting the compact package as a full run directory.
The supplementary saved-evidence hash checker also passed. This report is
excluded from proof input fingerprints.

- Complete result SHA-256: 14d3ed86f26b023d069493c636802220d453b33081d19bb472c1cf8b70b93547
- Input fingerprint SHA-256: 136b65168b463f01ccaf50749bddbbfbfa115a4c8431ba920b59727d0ac69c76
- Audit result SHA-256: 4686e2206cb18f2b42999acf74f19dc44f38a00c53c54b18968330979c179b72
