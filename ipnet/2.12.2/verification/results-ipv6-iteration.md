# Local verification results — ipnet 2.12.2

Accepted run: **2026-10-16**, [check-dxnxYoEp](runs/check-dxnxYoEp/result.json).
The full verifier passed with **588 audited theorems: 142 public contracts and
446 helpers**. All previous 403 theorem identities are retained. This adds
30 public contracts and 155 helpers. Contracts include family specializations;
these counts are not counts of distinct Rust method names. Astra independently
defined/reviewed specifications and acted as oracle; Sol proved the actual
extracted bodies. The primary reviewed statements, mappings, model boundaries
and the complete reproducible evidence.

## Newly accepted IPv6 range and numeric operations

- All nine Ipv6AddrRange overrides: next, next_back, nth, nth_back, last, min,
  max, count and size_hint. Contracts cover all raw endpoint pairs, including
  empty states and the full 2^128-cardinality range. Steps/skips describe both
  returned addresses and the independent half-open remaining interval.
- After exhaustion, any finite mixture of next/next_back/nth/nth_back returns
  only None and remains empty. This composes actual call equations, not merely
  a pure interval model. Skip indices range over every Usize.
- count returns the exact cardinality when it fits Usize and otherwise has the
  modeled checked integerOverflow failure. The Usize-sensitive contracts have
  an explicit 64-bit premise. nth/back and size_hint work for the full IPv6
  range; no U128 representation of 2^128 is assumed. This is not a promise of
  saturating count or release-profile overflow behavior.
- ipv6_mask_to_prefix and Ipv6Net::with_netmask completely classify contiguous
  masks, including zero/all-ones and rejection of noncontiguous masks.
  with_netmask preserves the original stored host bits.
- All three IPv6 arithmetic overloads and all four bitwise overloads have
  independent numeric contracts. Addition/subtraction saturate as specified;
  address/address subtraction returns a U128 difference. Concrete Ipv6Net
  Default returns zero address with prefix zero.

## Actual IPv6 subnet enumeration

The actual Ipv6Subnets::next has a complete raw-state classification:
reversed endpoints return None unchanged for every stored minimum prefix;
live q<=128 returns the largest aligned eligible CIDR block and exact residual;
live q>128 takes the modeled unwrap panic path. The minimum prefix is preserved.

Unconditional final trace theorems connect every Some call and terminal None
call to finite enumeration. They establish exact union, canonical blocks,
ascending order, pairwise disjointness and a decreasing remaining interval.
The intermediate LiveLaw premise is discharged using the actual next theorem.
Starting from a possibly noncanonical valid network and p<=q<=128, the actual
subnets constructor and calls produce the exact indexed list of 2^(q-p) blocks.
These lengths are mathematical Nat values, including 2^128; no Vec allocation
or collect-success claim follows.

## Full-family tagged dispatch

All nine IpAddrRange overrides and IpSubnets::next now have actual-body
contracts for BOTH V4 and V6. They preserve concrete returned tags and exact
raw updated states and compose independent concrete-family observations.
Empty intervals retain their family. Tagged count preserves the V6 overflow
classification; tagged subnet next preserves invalid-live panic. Nine range
methods and one subnet method are ten public mappings, not doubled by branch.

See [independent specification](ipv6-iteration-specification.md),
[coverage and exclusions](ipv6-coverage.md), and the archived
[403-theorem baseline](results-ipv6-network-values.md).

## Trust and remaining work

The pinned ipnet 2.12.2 upstream source is unchanged. A narrow standard
Ipv6Addr::new model concatenates eight U16 big-endian byte pairs; the exact
inherent selector required a recorded Charon matcher compatibility fix.
The new U128 trailing_zeros model uses fixed-width reversal/leadingZeros;
actual trailing_ones and all selected application bodies remain extracted.
Kernel proofs establish model mathematics and application contracts; the
reviewed Rust layout/intrinsic correspondences remain trusted boundaries.
New saturating-value/MAX+1 lemmas prove facts about existing scalar models.
See [model ledger](model-boundaries.md), [tool pins](toolchain.json), and
[extraction notes](extraction-notes.md). Axiom audits do not prove the
Rust-to-LLBC-to-Lean translation or source/model correspondence itself.

There are zero selected-but-unproved inventory entries, but **IPv6 as a whole
is not yet verified**. Remaining obligations include actual aggregate algorithms,
text parsing/formatting, Hash, optional serde/schemars integrations, tagged mask
dispatch/IpNet::with_netmask, unselected tagged derived traits, inherited methods
and consumers. The parser borrowed-callback and tagged mask namespace-shadow
limitations remain recorded. Existing network contracts retain their stated
valid-prefix domains; invalid new_assert behavior and arbitrary invalid network
states are not silently covered. Concrete raw iterator contracts explicitly
state their broader domains.

No new ipnet bug was found. The existing [bug records](bugs/README.md), including
optional-feature findings, remain available for later upstream PRs. No push,
issue, PR, evidence upload or publication occurred.

## Reproducible evidence

- Pinned unchanged source/release/Gitlink/build surface, exact tool patches,
  standard source boundaries and executable hashes all passed.
- Fresh extraction byte-matched every maintained generated model.
- Clean Lake build, all 588 theorem/mapping/transitive axiom checks and eight
  kernel shift checks passed. Only propext, Classical.choice and Quot.sound
  are permitted; no sorry, custom or native-decision axiom is accepted.
- Native default and no-default-features each passed 33 unit + 23 integration
  + 56 doc tests (112 each), separately from formal proof.
- Before/after input fingerprints match. The primary independently rechecked
  every saved artifact hash, the current fingerprint, all previous 403 theorem
  identities, uniqueness and the absence of selected-but-unproved entries.

The first full attempt, check-gYGsaciI, stopped at an inventory namespace typo:
IPv6SubnetIterator.next_live_spec instead of IPv6SubnetStep.next_live_spec.
The theorem body was unchanged. The corrected entry and all remaining leaf
checks passed, then the complete fresh check-dxnxYoEp run passed. The failed
run is retained; it is not counted as accepted evidence.

Run `bash ipnet/2.12.2/scripts/verify.sh` from repository root. Evidence is local
in the ignored run directory. This report is excluded from fingerprints.

- Complete result SHA-256: 004fc63a98a4c60812f41e3f1441e24cbcba4eed493358cce297e3394841bd5c
- Input fingerprint SHA-256: d799fb363b54b58f4414dbcb0b39cbf45c43d3c34a53ea6036f03d966461d3dc
- Audit result SHA-256: 07bab9dba6f2ee5e548751ab6fc2c4ca3b0f723803e538e0b58bc9f6cc48810a
