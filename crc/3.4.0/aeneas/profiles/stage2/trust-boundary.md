# Stage 2 frontend normalization: independent representation review

## Scope and status

This review assesses a proposed type-only LLBC normalization for the actual
crc 3.4.0 built-in implementations. It is an additional trusted frontend step,
not a proof of Charon, Aeneas, or the normalization program. Compiler binaries
remain pinned; upstream Rust and the complete application computation remain
unchanged. Acceptance of a concrete adapter additionally requires the structural
checks below; a design argument is not a claim that arbitrary adapter code has
been verified.

The original generic LLBC inspected is
`work/generic01/original.llbc` (Charon version 0.1.291). It contains actual
source text and types corresponding to upstream `src/lib.rs:58–80`. Its Crc
and Digest declarations are IDs 2 and 3, and the built-in Implementation impl is
ID 7 in this particular extraction. These IDs are observations, not stable
identifiers to infer across extractions.

## Exact source equations

The inspected built-in implementation has no methods, and declares

    <Table<L> as Implementation>::Data<W> = [[W; 256]; L].

Its associated-type binder uses a bound W parameter, while L is the enclosing
free const parameter. Substitution must respect these distinct binder levels.
It is not valid to replace every associated-type projection named Data without
checking that it belongs to this precise built-in implementation.

After choosing a concrete storage type W in {u8,u16,u32,u64,u128}, the source
value shapes are

    Crc<W,Table<L>> = { algorithm: &'static Algorithm<W>,
                        data: [[W;256];L] }
    Digest<'a,W,Table<L>> = { crc: &'a Crc<W,Table<L>>, value: W }.

A normalized Crc_W<L> and Digest_W<'a,L> must have exactly these fields in this
order, preserving field identities/indices, const L, shared references and their
regions. Algorithm retains every field, including metadata check/residue. The
contents of data are unrestricted; no table coherence or parameter validity is
introduced by normalization.

## Representation bijection argument

For each fixed W,L, map a source Crc value to the normalized record by retaining
its algorithm reference and the identical nested-array value. The inverse map
reassembles the source record using the associated-type equation. Both
compositions preserve every field exactly. Similarly map a Digest by retaining
its value and corresponding shared Crc reference. Reference identity, sharing
and lifetime structure are preserved under this type renaming; copying pointee
values or manufacturing new references would not satisfy the argument.

Concrete scalar W and Table<L> contain no borrowed data, so the source
outlives requirements W:'a and Table<L>:'a are satisfied. This does not permit
removing the Digest's actual borrow region or changing its shared/mutable
reference operations. Generic source type parameters W,I can be eliminated only
in declarations specialized to these exact choices; custom implementations
have no such representation equation.

The bijection covers malformed algorithm parameters and stale cached tables as
well as normal values. Excluding them here would silently weaken behavior.
Semantic CRC contracts may later impose bounds/coherence, independently of this
representation conversion.

## Required adapter checks

The surrounding extraction must retain original and normalized LLBC, source
fingerprints, adapter bytes/hash, configuration and a deterministic report.
The report should establish these concrete checks, failing closed on mismatch:

1. Recognize exact source declarations and the built-in associated-type equation;
   preserve all unrelated declarations and only specialize selected built-in
   Crc/Digest uses.
2. Compare each retained function signature/local type and body under the
   explicitly recorded type substitution and consistent metadata-ID mapping.
   Statement order, branch conditions, loop structure, arithmetic, constants,
   bounds checks, panic/error paths, call targets, call order and borrow actions
   must match. Type annotations or type arguments on the same calls may change;
   replacing their computational behavior may not.
3. Preserve field positions and reference regions, as well as generic const L
   and the distinction between free and associated-type-bound parameters.
4. Resolve all affected concrete Data projections. Remove methodless GAT
   metadata only when a complete reference scan shows no surviving projection,
   trait reference, call, generic clause or bound depends on that metadata.
   Removing a trait with computational methods, or hiding an unresolved opaque
   operation, is outside this review.
5. Check resulting declaration IDs/references are valid and no custom
   Implementation use has been silently reinterpreted as Table. A missing or
   unknown shape is an error, not a cue to discard the item.
6. Regenerate normalized LLBC and Lean from the exact source in the final
   verifier, compare retained generated output byte-for-byte, and audit proof
   roots independently of this transformation report.

Metadata reindexing must be bijective for retained items; removed metadata must
be demonstrably unreferenced. Deleting unused generic type declarations is
acceptable only after all uses have been replaced and the removal is explicit.
This is not permission to discard a failing selected method or dead-looking
branch. In particular L-dependent branches remain actual source branches unless
an independently justified compiler transformation handles them.

## What the resulting proofs mean

A Lean proof then establishes a theorem about actual source-backed generated
bodies **conditional on** the Rust→LLBC translation, this reviewed normalization,
and the LLBC→Lean translation and primitive models. The extra transformation
belongs in reported trusted assumptions. A structural diff and a bijective
representation argument provide review evidence, not a machine-checked
semantics-preservation theorem for the translator.

Coverage is restricted to built-in Table<0>, Table<1> and Table<16> methods at
the selected storage widths. Keeping const L generic in the normalized IR does
not establish source-callable methods for arbitrary unsealed lanes. No claim is
made for user-defined Implementation, arbitrary generic Clone dictionaries or
re-exported dependency APIs. Any later adapter extension outside this narrowly
reviewed substitution requires separate review.

The canonical CRC obligations in SPEC.md remain unchanged. A type normalization
may unblock extraction; it cannot establish polynomial encoding, byte injection,
current-table coherence, arbitrary-message processing or public checksum/update
correctness by itself.

## Concrete adapter review: first-order data parameter

The implemented `scripts/normalize-gat.py` uses a slightly more general type
encoding than the initial design above: it retains generic W and I and adds an
explicit third type parameter D to Crc and Digest. Within these declarations,
Crc's data field becomes D and Digest's Crc reference passes the same D. At
every retained concrete built-in use, the adapter supplies D=[[W;256];L]. This
is a first-order encoding of the associated type, not width-specific monomorphic
record generation. On this constrained image the same fieldwise bijection
applies. Arbitrary normalized choices of D do not imply additional Rust API
coverage; the source correspondence requires exactly the supplied array type.

The concrete original/normalized LLBC was inspected along with the normalizer
and independently authored `scripts/check-normalization.py`. All 101 function
declarations are retained. The checker compares full function trees, including
branches, calls, locals, arithmetic and error behavior, with only recognized
Crc/Digest type-reference changes. No function computation is replaced by a
model. The erased Implementation declaration and built-in implementation are
methodless; the checker scans retained runtime/type structures for unresolved
GAT references.

Review identified a completeness gap in the initial independent checker: it
checked selected type fields/generics but skipped the remaining Crc/Digest type
metadata, notably layout expressions. Actual changes in those expressions are
consistent with the intended type substitution (OffsetOf references and
SizeOf/AlignOf/inhabited uses of the associated type), but the initial checker
did not verify them. The requested correction is to traverse all remaining type
keys and validate the exact original projection-to-D rule under the Crc type
context, including layout. Acceptance of the complete structural claim requires
that correction, rather than describing the skipped metadata as already checked.

The layout gap was corrected and the revised checker was independently rerun:
**101 complete function declarations and 414 recognized type references pass**,
including remaining Crc/Digest type metadata and layout expressions. The
observed original SHA-256 was
`2e2d1f86c20e53cfc715fc9b9f690c58e7eb26dc746845d90d14f7c0310b0ad4`,
and normalized SHA-256 was
`98a03513a616b2c0989832a2b4a94bde944574c9942f7b633a9a2289a4689de3`.
This review accepts the concrete transformation for the constrained built-in
image described above, with the explicitly stated frontend trust boundary.
A final defensive request was to reject extra keys at the top-level JSON,
translated-crate and specialized-generics schema levels; no such extra keys
occur in the inspected pair. Final verifier evidence identifies the exact
checker version and fresh-run hashes.

Separately, `Stage2Proofs/ByteMath.lean` was reviewed against SPEC: its incoming
bit recurrence and explicit MSB-first eight-bit list match the independent
full-width, unreflected model. Its byte-injection invariant carries the XOR of
the unconsumed shifted byte, which vanishes after eight steps. TableValid then
relates lookup to canonical byteStep, and list induction lifts that relation to
arbitrary messages. These are noncircular mathematical bridges; their existence
alone does not prove an extracted public update or checksum body.

## Local display-name alpha-renaming

A further normalization changes only the local display name `table` to
`lookup_table` in five private table-construction functions, avoiding a generated
Lean namespace collision. The source LLBC variable indices, types, spans,
reference operations and computations are unchanged. The checker permits this
only at a function-local `.../locals/locals/<index>/name` path, under the crc/table
module, and checks the original locals have no `lookup_table` collision.

Independent rerun reports exactly (function,local) pairs (69,16), (70,16),
(71,16), (72,16), (73,16), alongside 101 full function comparisons and 414 type
references. The corresponding normalized `crc_body.llbc` SHA-256 is
`05dcb633b316ced9295c01f88d95dc5c9f2978f7c66511d07cffd2648abab4d6`.
This alpha-renaming is accepted as part of the declared trusted frontend step;
no runtime variable index or program operation is renamed/replaced.

## Public8 and Refout8 contract review

`CrcBody.checksum8_canonical` and `digest8_protocol_canonical` implement the
independent canonical model at storage/algorithm width 8, with refin=false and
refout=false. The `CrcRefout8.checksum_canonical` and
`digest_protocol_canonical` statements genuinely broaden refout to either value:
compute canonical MSB-first run, reverse the resulting eight bits iff refout,
then XOR xorout. Poly/init/custom initial/xorout are arbitrary U8 values; oddness
is unnecessary, and the input slice is arbitrary, including empty. Table<1>
coherence is an explicit hypothesis, not inferred from merely having a Crc
value. Thus public algorithm replacement is handled by requiring the current
polynomial's table relation. This review does not presume constructor coherence
has already been proved in another module.

The actual Digest update statements preserve the entire retained Crc and return
the independently defined run from the arbitrary supplied state. The append
statement asserts success of all three actual updates and equality of the final
digests, including empty chunks; it is stronger than a pure model append lemma.

The especially general `CrcRefout8.digest_update_canonical` drops even the width
and refin hypotheses because Table<1>/u8 lookup itself ignores them. Its
`Coherent8` predicate still specifies an **unreflected eight-bit** lookup table.
This is a sound conditional operational statement, but must only be advertised
as CRC correctness for the algorithm named by the public fields when width=8
and refin=false also hold. It is not canonical correctness for arbitrary width
or arbitrary refin. Refout is irrelevant to update and remains unrestricted.
