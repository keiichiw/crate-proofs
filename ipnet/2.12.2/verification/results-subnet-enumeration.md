# Local verification results — ipnet 2.12.2

Accepted run: **2026-10-16**, [check-rgPh4e3G](runs/check-rgPh4e3G/result.json).
The complete verifier passed with **340 audited theorems: 67 public contracts
and 273 helpers**. All previous 283 theorem identities are retained. This adds
one public API form, Ipv4Subnets::next, and 56 helpers. Under the existing generic
contains mapping convention, 67 contracts correspond to 64 API forms.
Astra independently specified/reviewed; Sol proved actual extracted bodies.

## Completed IPv4 subnet obligations

`IPv4SubnetAll.next_raw_spec` classifies every raw endpoint pair and U8 prefix:

- Reversed/empty interval: normal None, unchanged state, for every q.
- Nonempty interval with q≤32: normal Some of the exact greatest aligned CIDR
  that fits and respects q. Stored address is the original start, prefix matches
  the independent bestPrefix, updated remaining interval is exact, and q is preserved.
- Nonempty interval with q>32: the modeled Rust unwrap panic, not ordinary Err
  or a claimed successful execution. This previously known domain is not a new bug.

The proofs include unaligned starts, zero, singleton MAX, full IPv4 range,
all valid prefixes and saturation/exhaustion updates. The mathematical choice is
independent of the implementation's bit counts. Selected block and remainder
partition the input, and the Nat remaining length decreases on each Some.

`IPv4SubnetActualTrace` discharges its intermediate LiveLaw using the actual
checked next theorem. Its final theorems have no assumed implementation-correctness
premise. For q≤32 they construct a finite trace of actual next calls, including
terminal normal None, with at most the initial Nat cardinality successful calls.
Outputs are canonical, ascending, pairwise disjoint, and their union is exactly
the original interval. Empty states do not revive by the actual empty-next law.

For every valid, possibly noncanonical network n with prefix p and p≤q≤32,
the actual subnets(q) constructor followed by actual next produces exactly
2^(q-p) networks. Output i is (lower(n)+i*2^(32-q),q); indexed observations
are None beyond that count, and the trace ends with actual None. The earlier
constructor's ordinary error cases remain proved. These composition theorems
are audited helpers supporting existing subnets coverage, not additional API
names. Logical finite lists do not assert successful allocated Vec collection.

## Boundaries and remaining work

No new semantic model was added in this stage. The reviewed trailing-zero model
from the [previous checkpoint](results-subnet-helpers.md), existing concrete
address/comparison, scalar, memory, Array/Slice models and Rust→LLBC→Lean translation
remain explicit trust boundaries. Address equality is now connected through
kernel-checked big-endian value injectivity and existing Array/Slice models.
Rust/model correspondence itself is not proved by an axiom audit. See the
[model ledger](model-boundaries.md) and [independent subnet spec](ipv4-subnets-specification.md).

Prior IPv4 contracts and 64-bit restrictions on Usize-sensitive range methods
remain as described in [results-ipv4-core.md](results-ipv4-core.md). The coverage
ledgers captured by this run describe the preceding baseline; this result
supersedes their pending-subnet statements. Zero selected-but-unproved entries
means selected extraction coverage, not whole-crate coverage.

Remaining: aggregate, textual parsing/formatting, unmapped traits/tagged dispatch,
generic consumers/allocation, optional serde/schema integration and other-family
iteration. Aggregate and parser probes are diagnostics only. The user resumed
after known IPNET-003; no further ipnet bug was found in this stage. Existing
[bug records](bugs/README.md) remain available for later upstream PRs. No source
patch, issue, PR, upload or publication to ipnet occurred.

## Reproducible evidence

- Source/release/Gitlink/build-surface/tool/binary/exact-patch checks passed.
- Fresh extraction byte-matched every maintained model.
- Local Lake clean/rebuild, all 340 theorem/mapping/transitive axiom checks and
  eight kernel shift examples passed. Only propext, Classical.choice and
  Quot.sound are allowed; no sorry, custom or native-decision axioms.
- Native default and no-default-features each passed 33 unit + 17 integration
  + 56 doc tests, separate from formal proof.
- Before/after fingerprints match. Primary independently rechecked every saved
  artifact hash, current fingerprint and retention of all previous 283 identities.

Run `bash ipnet/2.12.2/scripts/verify.sh` from repository root. Evidence stays
local in the ignored run directory. This report is excluded from fingerprints.

- Complete result SHA-256: 7877b3461616cb20dfcb93c66e25cdd522dde8ff335d51cfd4a6f9cd5b61acef
- Input fingerprint SHA-256: 29013f6d70d41a1f4aaefbf5fa190a86fc390a50f646068f99d65375455410be
- Audit result SHA-256: 1921e8f91d94a61f886043318c2a9a70a621503c940f758abffdf342d6149fa5
