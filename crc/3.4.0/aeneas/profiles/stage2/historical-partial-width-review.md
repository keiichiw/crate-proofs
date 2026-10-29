# Independent review: partial-width canonical CRC

## Decision

The proposed physical-register model agrees with the independently specified
RevEng/Rocksoft width-w CRC **as a representation refinement**, provided the
encoding and observation equalities below occur in the checked proof chain.
It must not replace the target with a degree-N CRC whose shifted polynomial
merely happens to produce the same test vectors. The independent target remains
the width-w incoming-bit recurrence in SPEC.md.

The source provenance is unchanged: the investigator previously read the
[RevEng parameter definitions](https://reveng.sourceforge.io/crc-catalogue/legend.htm)
and [Rocksoft model description](https://www.zlib.net/crc_v3.txt). Input reflection
changes per-byte bit order, while output reflection applies to the width-w
canonical state before final XOR. The proof review uses those conventions.

## Encoding and transition relation

Let N be the storage width and 1<=w<=N. Let p and r be BitVec w values and define

    E(r) = zeroExtend_N(r) << (N-w),
    pPhysical = E(p).

The physical state is MSB-aligned even when input bits are fed LSB-first.
The same external bit recurrence can be evaluated at width N using pPhysical.
The reviewed `WidthEncoding.lean` definitions and statements establish that

    E(inputStep_w(p,r,b)) = inputStep_N(E(p),E(r),b),

because encoding preserves XOR, commutes with one left shift, and carries the
canonical top bit w-1 to the physical top bit N-1. No polynomial oddness is
needed. The generic fold-over-bits theorem consequently applies to either
MSB-first or LSB-first byte lists. Its instantiated byte/message theorem for
refin=true must use the LSB-first list; the currently inspected `encode_run`
statement is explicitly the unreflected list and does not alone cover refin.

The physical polynomial has N-w zero low bits. It is an encoded feedback mask,
not a replacement standard polynomial parameter. Width-one, widths below eight,
width N itself, and the 82-bit algorithm stored in u128 all follow the same
representation relation; the byte-injection theorem at physical storage width
requires N>=8, which all five actual storage types satisfy.

## Endpoints that must be checked

For every canonical state r, prove exact BitVec equalities

    E(r) >>> (N-w) = zeroExtend_N(r),
    reverse_N(E(r)) = zeroExtend_N(reverse_w(r)).

These equalities justify the proposed observation

    physicalFinish(S) =
      (if refout then reverse_N(S) else S >>> (N-w)) XOR xorout

when S=E(r). The result is exactly zeroExtend_N(canonicalFinish(r)) for bounded
xorout, not merely congruent modulo 2^w. `refout` and `refin` remain independent.
Neither optional output reflection nor truncation is silently omitted.

For refin=false, the implementation's stored state equals S. For refin=true,
its stored state V satisfies reverse_N(V)=S (equivalently V=reverse_N(S)). This
must hold initially, after every input byte and after every update; equality of
final outputs on a test vector is insufficient. The reflected polynomial used
by Rust must equal reverse_N(E(p)). Thus both physical paths feed the same
canonical state machine, with their prescribed per-byte input order.

For arbitrary raw N-bit custom initial j, prove

    j << (N-w) = E(j.setWidth w),
    reverse_N(j) >>> (N-w) = reverse_N(E(j.setWidth w)).

These formulas describe the actual raw initialization operations, including
high bits outside w. Requiring j<2^w would unnecessarily weaken the custom
initial contract. Algorithm init may be bounded in the standard validity
predicate; a generalized initialization theorem may explicitly use its low-w
projection instead.

## Required public hypotheses

A standard canonical checksum theorem uses 1<=w<=N, polynomial<2^w,
algorithm.init<2^w and xorout<2^w, with both reflection flags arbitrary. The
BitVec w representation makes polynomial/state bounds intrinsic after conversion,
but the theorem must connect raw algorithm fields to that conversion. It must
not silently reinterpret an unbounded raw polynomial as the specified value.
Even/zero bounded polynomial values remain algebraically valid. Metadata check
and residue are irrelevant to the computation.

Update alone needs the width/polynomial relation and an encoded starting state;
it does not need bounds on unused init or xorout or a restriction on refout.
When arbitrary stored words are allowed in a raw loop theorem, a canonical CRC
corollary must add the encoding predicate. Only full-width state representation
is automatically surjective over all storage words.

Table modes additionally require the current table's correspondence to current
(w,p,refin). Constructor-produced coherence should be discharged by the actual
constructor theorem. A public algorithm-field replacement may invalidate it.
NoTable has no cached table assumption. The independent table meaning remains

    table[k][b] = store(run_w(byteStep_w(0,b), k zero bytes)),

where store(r)=E(r) for refin=false, or reverse_N(E(r)) for refin=true. In
particular a mathematical helper table-validity assumption must eventually
match the actual array and current algorithm, not an unrelated function.

The theorem must quantify arbitrary finite representable input slices and
preserve the entire retained Crc across actual Digest updates. Incremental
composition asserts success and equal resulting states for actual split and
whole computations; it cannot be replaced by only a model fold-append theorem.

## Claim boundary

The reviewed `WidthEncoding.lean` currently supplies the MSB canonical
transition/fold/byte/message representation equations. A complete partial-width
public claim additionally requires the reflected bit-order instantiation,
initial and output endpoint equations, source-backed update/table relations,
and composition into actual public checksum/Digest operations. An intermediate
physical-register theorem is useful and independent of Rust implementation
structure, but is not advertised as canonical width-w correctness before those
checked links are present.
