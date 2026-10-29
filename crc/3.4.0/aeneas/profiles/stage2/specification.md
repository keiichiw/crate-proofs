# Stage 2: canonical checksum and incremental-update contracts

This stage targets successful computation of the external CRC model by actual
public `Crc::checksum` and `Digest::update` bodies. These are goals, not an
announcement of proved coverage. The stage-local theorem inventory and results
must identify each accepted restriction. Baseline evidence is left unchanged.

## Independent specification provenance

The specification investigator previously read these sources, independently of
implementation proof construction:

- Ross N. Williams, *A Painless Guide to CRC Error Detection Algorithms*, v3,
  sections 13–15: <https://www.zlib.net/crc_v3.txt>.
- RevEng catalogue model parameters:
  <https://reveng.sourceforge.io/crc-catalogue/legend.htm>.
- crc 3.4.0 public contracts: <https://docs.rs/crc/3.4.0/crc/struct.Crc.html>
  and <https://docs.rs/crc/3.4.0/crc/struct.Digest.html>.
- Parameter definition adopted by the crate:
  <https://docs.rs/crc-catalog/2.5.0/crc_catalog/struct.Algorithm.html>
  (the previously read latest documentation resolved to 2.5.0).

These sources establish a direct register model: input reflection determines
bit order within each byte; output reflection and final XOR follow message
processing. No final block of zero bits is appended. The inherited source
interpretations and identified wording errors are recorded in
`../../verification/SPEC.md`. This stage restates the mathematical model and
strengthens the required connection to public methods; it does not replace the
external model with a copy of a generated loop.

## Model and domain

Storage width N is 8, 16, 32, 64 or 128. Parameters are algorithm width w,
polynomial p, initial value i, input reflection ri, output reflection ro and
final XOR x. A valid canonical algorithm satisfies

    1 <= w <= N,  0 <= p,i,x < 2^w.

Both reflection flags vary independently. The standard catalogue polynomials
are odd, but the recurrence and desired implementation theorem also cover
bounded even and zero p. Do not add oddness to avoid a proof obligation.
`check` and `residue` are unrestricted metadata for computational contracts.
A mathematical byte lies in 0..255. Finite messages include empty input and
are not restricted to catalogue examples, a bounded test corpus or any fixed
number of bytes. Machine inputs are actual representable slices.

Let bit_j(v)=(floor(v/2^j) mod 2), and let rev_w reverse precisely w low bits.
With r a canonical w-bit register and b in {0,1}, define

    step(r,b) = ((2*r) mod 2^w)
                XOR (if bit_(w-1)(r) XOR b = 1 then p else 0).

For byte c, let bits_ri(c) be [bit_7(c),...,bit_0(c)] when ri=false and
[bit_0(c),...,bit_7(c)] when ri=true. Define

    byteStep(r,c) = foldl(step, r, bits_ri(c))
    run(r,A) = foldl(byteStep, r, A)
    finish(r) = (if ro then rev_w(r) else r) XOR x
    checksum(A) = finish(run(i,A)).

The checksum output is a w-bit value represented in the low bits of the return
word; it is not left-aligned. The generator polynomial has implicit leading
coefficient X^w. This specification is mathematically independent of the table
layout, raw word helpers, generated monads and any proposed extraction patch.

## Representation and coherence

The canonical state r is represented internally by

    E(r) = if ri then rev_w(r) else r * 2^(N-w).

A predicate `Rep(a,d,r)` means d retains the designated Crc object c with current
algorithm a, and its stored value is E(r), where 0<=r<2^w. Equalities of references
are interpreted through the actual extracted representation; specifications
must preserve the entire relevant Crc value, not just a polynomial field.

For Table<L>, L in {1,16}, define `Coherent(c)` by every actual entry obeying

    c.table[k][j] = E(run(byteStep(0,j), replicate(k,0)))
    for 0<=k<L and 0<=j<256,

using c's **current** (w,p,ri). For NoTable, coherence is true without premises.
Constructors must establish this relation if their results are used to discharge
it; a conditional table-update proof alone does not verify construction.

`Crc.algorithm` can be assigned after construction. Such assignment may break
coherence, as the baseline counterexample demonstrates. Thus “was constructed
by new” alone is insufficient. The theorem may accept any coherent object,
including one whose algorithm was changed while preserving the table relation.
Changes only to init/refout/xorout/check/residue do not change table coherence.
NoTable computation follows the current algorithm and needs no cached invariant.
An active Digest borrows Crc, so ordinary safe Rust cannot simultaneously mutate
that Crc through an exclusive reference; the incremental theorem keeps the Crc
fixed throughout the update sequence.

## Required public contracts

Each generated-function statement must assert actual total success:

    exists out, generatedFunction(args) = Result.ok(out) and Post(out).

Use the generated mutable-borrow output shape rather than a surrogate Rust
function or model-only equality. A pure expression naming the expected checksum
is insufficient unless equality to the actual generated public body is proved.

### Crc::checksum

For every valid current algorithm a, coherent Crc c, and representable slice A,

    actualChecksum(c,A) succeeds and its returned word equals checksum(A).

The result must be exactly the canonical low-w-bit checksum, not only a congruent
value, an uninterpreted recurrence or the existence of some output. No assertion
about the metadata `check` or `residue` is required. For NoTable this includes
objects with any previous construction/mutation history, subject only to the
current parameter requirements.

### Digest::update

For every canonical r, any digest satisfying Rep(a,d,r), coherent retained Crc,
and representable slice A,

    actualUpdate(d,A) succeeds with resulting digest d',
    Rep(a,d',run(r,A)), and d'.crc = d.crc.

Do not require r to arise from one selected constructor or prefix; quantify over
all canonical states. The update contract uses only w,p,ri. Bounds on init or
xorout and a choice of refout are unnecessary for update alone. They become
relevant when composing constructors or finalization. In particular, successful
update does not establish that finalization is the identity.

### Initialization and observation needed for composition

`digest_with_initial(j)` for any storage word j succeeds with state E(j mod 2^w).
This includes high bits outside w, and uses the current algorithm's representation.
`digest()` succeeds with E(i) for valid i. Finalizing any encoded canonical state
r succeeds and returns finish(r), for all four pairs (ri,ro). These contracts do
not require table coherence, although a subsequent table-based update does.

### Empty and incremental laws on actual computations

For update, A=[] succeeds and preserves both state and retained Crc exactly.
For checksum, A=[] succeeds and returns finish(i). For actual slices A, B and C
with list(C)=list(A)++list(B), prove success of all updates and equality of the
resulting digest values in

    update(update(d,A),B) = update(d,C).

The mathematical fold-append law is necessary but not sufficient: the equality
must concern actual successful generated calls and their mutable-state returns.
It should imply the corresponding final checksum equality after arbitrary split
points and, by induction, any finite list of chunks, including empty chunks.
No finalized checksum is passed directly as a new initial state: continuation
uses the internal state; resuming from a finalized result requires undoing
final XOR and output reflection.

## Practical first milestone and expansion

First preference is NoTable/u8, eliminating table coherence and constructor-table
proofs. Aim for all valid widths 1..8, arbitrary bounded parameters, independent
reflection flags, arbitrary message lengths and arbitrary canonical digest
states. If reflection extraction or width bridges remain blocked, an explicitly
named width=8, ri=false, ro=false theorem is a useful initial **restricted** public
contract. It must still cover arbitrary bytes, lengths, initial state and XOR;
it must not silently become the general theorem claimed above. A result for a
single fixed catalogue algorithm is a narrower fallback and must be labeled.

For full-width unreflected u8, the key independent byte lemma is

    byteStep(r,c) = eight zero-input polynomial steps starting at (r XOR c).

This relates input-bit feeding to the utility kernel proved in the baseline.
It is not true without the correct width/encoding and bit-order hypotheses.
With reflection or smaller width, establish the encoding and byte-injection
bridge explicitly; an outgoing-bit polynomial recurrence alone does not prove
that the public caller injected the correct byte or used the canonical polynomial.

Then extend reflection and narrow widths, NoTable wider storage, and Table<1>
with independently established table relation. Table<16> additionally needs its
sixteen-byte decomposition and remainder path. Do not impose an arbitrary
short-message limit to avoid loop termination. Generated index safety must be
proved from actual slice bounds; NoTable's i<len implies its i+1 is representable.
For lookahead loops, justify additions from genuine Rust slice bounds rather
than silently assuming every modeled usize-length sequence is addressable.

## Oracle and acceptance evidence

The baseline native oracle already implements the independent bit-input model.
Stage-local tests should exercise empty input, arbitrary split positions,
empty chunks, both reflection flags, w=1/w=N, custom initial high bits and
nonzero xorout, without treating successful examples as proof. Retain the
stale-table example separately so coherent-state preconditions remain visible.

Acceptance requires a source-backed extraction of the actual public methods,
checked correspondence for any primitive model/translator change, proofs of the
public total-success statements, clean regeneration and transitive axiom audit.
Only the established standard axioms are permitted. A user-authorized tool fix
may enable extraction; its existence does not establish the CRC math bridge.


The managed recorder adapter preserves all 655 original roots and adds 45 exact
word protocol specializations at fixed lanes 0, 1 and 16. Each new declaration
uses the original generic proof directly; its width premise and result equations
are unchanged. The trivial SupportedL premise is discharged by the chosen literal.
The audit therefore covers 700 roots while the 75 public mappings and combined
96/171 callable coverage remain unchanged. These wrappers add no mathematical
contract and do not establish the excluded sixteen-lane message computation.
