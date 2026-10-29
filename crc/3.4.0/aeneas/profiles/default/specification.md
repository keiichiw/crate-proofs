# Independent CRC specification (crc 3.4.0)

Specification investigation: 2026-10-20. This document states intended contracts;
it does not assert that every contract below has been proved. The maintained
proof inventory and results determine achieved scope.

## Sources actually read

- Ross N. Williams, *A Painless Guide to CRC Error Detection Algorithms*, version 3,
  19 August 1993, sections 13–15 and the model description:
  <https://www.zlib.net/crc_v3.txt> (author's text mirrored by zlib).
- CRC RevEng, Catalogue legend, “Model parameters”:
  <https://reveng.sourceforge.io/crc-catalogue/legend.htm>.
- Public crate parameter contract:
  <https://docs.rs/crc-catalog/latest/crc_catalog/struct.Algorithm.html>
  (resolved documentation version 2.5.0 when read).
- Public crc 3.4.0 contracts:
  <https://docs.rs/crc/3.4.0/crc/struct.Crc.html> and
  <https://docs.rs/crc/3.4.0/crc/struct.Digest.html>.
- Release discovery independently read <https://crates.io/api/v1/crates/crc>:
  `max_stable_version = 3.4.0`. Root source-identity evidence pins the exact source.

Direct shell fetches of Ross/RevEng/docs.rs were blocked by the environment proxy;
the pages above were successfully read through the web tool. The original Ross
URL was unavailable; the zlib mirror was readable. No claim is made that merely
trying an inaccessible URL constitutes reading its specification.

Source interpretation: Rocksoft separates per-byte input reflection from final
register reflection and final XOR. Its section 15 has a contradictory second
`FALSE` in the REFIN paragraph; RevEng's unambiguous true=LSB-first definition
resolves it. Width is the number of register bits, mathematically the degree of
the generator, or its binary representation length minus one. Do not interpret
the catalogue's “degree ... minus one” wording as a different polynomial degree.
The high polynomial coefficient is implicit. `check` and `residue` describe
observations, not transition parameters. [Rocksoft](https://www.zlib.net/crc_v3.txt),
[RevEng](https://reveng.sourceforge.io/crc-catalogue/legend.htm).

## Mathematical domain

Let the storage width be N in {8,16,32,64,128}. An algorithm comprises width w,
polynomial p, initial state i, input reflection ri, output reflection ro and
final XOR x. The standard domain is 1 <= w <= N, 0 <= p,i,x < 2^w, with p odd.
The leading polynomial coefficient is implicit: G(X)=X^w + sum p_j X^j over
GF(2). The transitions also make sense for even or zero p, so proofs may safely
cover the larger bounded-polynomial domain. Oddness must not become a needless
implementation-safety hypothesis. `check` and `residue` can be arbitrary storage
values for computational contracts; asserting their correctness is a separate
catalogue validation task. Message bytes range over 0..255, including an empty
message. Reflection booleans are independent, including ri != ro.

`Algorithm` has public fields; Rust types alone do not establish these bounds.
Invalid width (zero or larger than N) lies outside the CRC contract, and may
cause shift/subtraction failure. A claim covering all raw `Algorithm` values
must therefore separately describe failure behavior. High bits in custom
`digest_with_initial` inputs are allowed: initialization uses the low w bits.
High bits in algorithm `xorout` are excluded from canonical w-bit CRC claims;
a separate machine-level projection contract can allow them without claiming
a canonical checksum. [Algorithm contract](https://docs.rs/crc-catalog/latest/crc_catalog/struct.Algorithm.html).

## Canonical register model

All following arithmetic uses mathematical naturals and explicit fixed-width
operations. Define mask_w=2^w-1, bit_j(v)=floor(v/2^j) mod 2, and

    reflect_w(v) = sum_{j=0}^{w-1} bit_j(v) * 2^(w-1-j).
    feedback(r,b) = bit_(w-1)(r) XOR b.
    step(r,b) = ((2*r) mod 2^w) XOR (if feedback(r,b)=1 then p else 0).

This is the MSB-oriented feedback-register model. It is independent of the
crate's table layout, machine-width shifts and slicing-by-16 implementation.
For byte c, feed bits [7,6,...,0] if ri=false or [0,1,...,7] if ri=true.
`byteStep(r,c)` folds `step` over precisely those eight bits. Define

    run(r, []) = r
    run(r, c::cs) = run(byteStep(r,c), cs)
    finish(r) = (if ro then reflect_w(r) else r) XOR x
    checksum(bytes) = finish(run(i, bytes)).

There is no extra appended block of w zero bits in this direct-register model.
The incoming bit is XORed with the outgoing high bit *before* polynomial
feedback. This formulation works when w<8 as well as for full storage widths.
Its parameters and bit order follow the external model, rather than extracted
Rust. [RevEng model](https://reveng.sourceforge.io/crc-catalogue/legend.htm).

## State representation bridge

For canonical 0 <= r < 2^w define the storage representation

    encode(r) = if ri then reflect_w(r) else r * 2^(N-w).
    decode(v) = if ri then reflect_w(v) else floor(v / 2^(N-w)).

`decode` is an inverse on encoded states; it need not be an inverse on arbitrary
N-bit words. A digest represents r exactly when its stored value is `encode(r)`
and it retains the relevant CRC object. Initialization of custom storage word
j must produce `encode(j mod 2^w)`. Finalizing an encoded state must succeed and
return `finish(r)`, for all four combinations of ri and ro. A proof using only
raw `reverse_bits`/shift equalities is a useful representation contract, but is
not alone a proof of the complete checksum computation.

For any mathematical input list A and B:

    run(r, []) = r
    run(r, A ++ B) = run(run(r, A), B)
    checksum([]) = finish(i).

Finalization is an observation, not another input byte. Resuming from a finalized
checksum requires undoing XOR and output reflection first; passing a finalized
checksum directly to `digest_with_initial` generally does not resume the digest.
The latter overrides the algorithm's initial parameter in canonical orientation.
[Custom initialization contract](https://docs.rs/crc/3.4.0/crc/struct.Crc.html).

## Public API obligations and coverage priorities

The inherent API families exist for all five storage types and Table<L> with
L in {0,1,16}; the default is Table<1>, and NoTable aliases Table<0>.

| API | Intended total-success contract |
| --- | --- |
| `Crc::new` | Retains algorithm and constructs its valid table representation. |
| `Crc::table` | Returns exactly the stored table; this projection needs no table-validity hypothesis. |
| `Crc::digest_with_initial` | Returns a digest referring to this CRC and representing j mod 2^w. |
| `Crc::digest` | Same contract with j=algorithm.init. |
| `Digest::update` | For state r and bytes A, returns state run(r,A); preserves the CRC reference. |
| `Digest::finalize` | For encoded state r, returns finish(r), including empty-message states. |
| `Crc::checksum` | Returns checksum(A) for every representable byte slice A. |
| clone operations | Preserve observable algorithm/table/state values; separate from CRC arithmetic. |

Contracts for extracted functions should assert `exists out, actual = Result.ok out
and postcondition out`, not an equality permitting both sides to fail. Stateful
composition must use actual slices whose values concatenate, and assert success
of both paths. A model-only fold-append lemma does not prove `Digest::update`.

For a canonical table, lane k and byte j have independent meaning

    table[k][j] = encode(run(byteStep(0,j), replicate(k,0))).

Thus lane zero is one byte of CRC feedback from zero, and higher lanes append
zero bytes. Prove this against generated table construction before using it as
a hypothesis for generated lookup loops; do not declare table correctness as an
axiom. Slicing-by-16 requires a separate decomposition argument. Table<0> avoids
table construction and is a useful first full arithmetic target.

**Public mutable-field caveat.** `Crc.algorithm` is public while its table is
private. A caller may construct Crc with algorithm A and then replace the field
with B. For L>0 the stored table can then disagree with B. Therefore general
checksum/update contracts require that the current table matches the current
(width, poly, refin), or explicitly restrict to objects retaining that relation.
No table relation is needed for mere digest construction, finalization, or table
projection. Changing only init/refout/xorout/check/residue does not itself
invalidate table contents. For L=0 there is no stored table consistency issue.

Prioritize all-width projections, arbitrary custom initialization and finalization
with representation bridges; then establish an arbitrary-input bitwise core,
NoTable update and actual incremental composition; then table generation and
lookup/slicing implementations. A restricted full-width or equal-reflection
result must be labeled as such. Re-exported catalogue constants and `Algorithm`
traits are dependency APIs, not automatically covered by proofs of local methods.
