# Independent final contract review

This review reads the actual Lean statements and mathematical definitions; it
is not proof authoring or a substitute for the final fresh build and axiom
audit. Stage1 files/evidence were not changed by this review. The external model
and read-source provenance remain in SPEC.md and partial-width-review.md.

## Canonical definition accepted

`PartialSpec.checksum` aliases `FullWidthSpec.checksum` with the type parameter
instantiated to the **algorithm width w**, not the storage width N. Despite the
historical FullWidthSpec module name, its definition is generic in the register
width. `run` selects the MSB-first or LSB-first byte-bit list according to refin;
both lists feed the same MSB-oriented incoming-bit polynomial recurrence.
`finish` reflects precisely that w-bit canonical register iff refout, then XORs
the w-bit xorout. This is the independent RevEng/Rocksoft target.

`WidthEncoding` proves bit-transition/fold/MSB-byte/message correspondence under
1<=w<=N. `WidthEndpoints` supplies the LSB-first counterpart and exact endpoints:
MSB alignment followed by right shift returns zero-extended canonical state;
reversing the aligned storage word returns zero-extended width-w reflection.
Its raw initialization theorem covers arbitrary raw initial words by taking the
low w bits. Its finalization theorem handles all four refin/refout combinations
and returns exact zero-extended canonical output. No polynomial-degree change,
congruence-only conclusion or test-vector oracle substitutes for the target.

## Public root contract findings

The inspected `Partial8`, `Partial32`, `Partial64`, and `Partial128` public
checksum/update statements agree with that model. The explicit public `hp`
(or `_hp`) equation ties the raw current polynomial field to the zero-extension
of the canonical width-w polynomial. Even when unused in a table-loop proof,
this premise is semantically necessary to identify the exposed algorithm rather
than an arbitrary table's behavior. There is no odd-polynomial restriction.

Checksum roots require 1<=w<=N and a bounded xorout equation. Partial8's checksum
roots also require a bounded initial-value witness; Partial32/64/128 use an
explicit low-w projection of algorithm.init, thereby additionally describing
high initial bits. These are compatible contracts: they all cover standard
valid bounded init; claims about the generalized high-init domain must identify
which statement establishes it. No `check` or `residue` hypothesis is required.

The Table<1> roots explicitly require coherence: every byte-indexed stored entry
is the encoded canonical transition from zero using the current refin, width
and polynomial witness. This is not an assumption that the whole checksum
function is correct. The proofs use independently established one-byte table
semantics to derive arbitrary-message behavior. However, these roots alone do
not prove that `Crc::new` constructs such a table. A report must distinguish a
conditional coherent-object theorem from any separately checked constructor
composition. Public algorithm reassignment can break coherence; the hypothesis
correctly keeps that observed issue in scope.

NoTable roots require no cached-table relation. They obtain the physical
polynomial from the actual source initialization operations and compose the
actual generated update loops. Their polynomial premise refers to the current
algorithm; there is no hidden assumption about the object's construction history.

Digest update roots quantify an arbitrary canonical width-w state and require
that the actual raw stored word is its encoded representation. This is essential
when w<N: arbitrary N-bit words need not be canonical encodings. Their outputs
preserve the complete retained Crc and equal the encoded canonical run. They do
not restrict states to one chosen prefix, catalogue polynomial or initial value.
Bounds on unused init/xorout and restrictions on refout are correctly absent.

All these strongest public statements assert an existential successful actual
`Result.ok` execution, not just a pure-model equality or termination conditional
on success. Input is an arbitrary represented `Slice U8`; there is no test-corpus,
fixed-length, nonempty or short-message premise. Empty checksum therefore has
its correct initial-state/finalization value, and empty update preserves encoded
state. Reflections are independent booleans in the partial-width roots.

## Scope and review status

At the initial review snapshot, Partial32's Table<1> public checksum/update
roots were complete, and its NoTable internal update theorem was present;
Partial8/64/128 contained both Table<1> and NoTable public roots. Partial16's
checked source contained the encoded Table<1> update helper while its public
wrappers were still being completed. Final inventory/build evidence must decide
which completed roots count; this document does not promote an in-progress file
to an accepted theorem. Later review updates below record completed additions.

These partial-width files concern Table<1> and NoTable. They do not establish
Table<16> slicing correctness. Mathematical append laws or a public composition
theorem in another module must not be counted as a new API instance. Conversely,
actual successful split-update equality is a useful separate contract and
should retain the source-level mutable-state result.

No semantic defect or weakened canonical target was found in the inspected
strongest roots. Acceptance remains conditional on the documented translation,
primitive-model and reviewed normalization trust boundaries, and the final
successful regeneration/build/transitive-axiom audit.

## Completed roots and inventory follow-up

Subsequently inspected the completed Partial16 public `checksum_table1`,
`digest_update_table1`, `protocol_table1`, `checksum_notable`,
`digest_update_notable` and `protocol_notable` statements, and the added
Partial32 `checksum_notable` and `digest_update_notable` statements. They satisfy
the conclusions above. This supersedes the earlier in-progress snapshot note.
Partial16, like Partial8, requires bounded algorithm init for its direct
checksum root; its custom-initial protocol takes arbitrary raw initial words
and explicitly projects to width w. Both flags and arbitrary slices remain
unrestricted. Partial32 NoTable uses low-w algorithm init and no coherence
premise. No additional semantic correction was needed.

The independently checked inventory snapshot has 73 distinct stage2 mapped
public API instances and 171 coverage rows, of which 94 are marked formal:
21 baseline plus 73 stage2. Every mapped theorem declaration exists in its
specified module; each mapping's theorem and precondition text agrees with its
coverage row. This is a structural/domain review, not the transitive audit.
The ten checksum and ten Digest-update rows refer to NoTable/Table<1> for all
five storage widths. Their domain text distinguishes bounded polynomial,
checksum xorout/init conditions, encoded incoming state, current table coherence,
both reflection flags, and arbitrary represented slices. Word-level endpoints
on Table<16> are not counted as message-computation correctness.

Constructor rows correctly restrict the accepted construction/coherence result
to full algorithm width equal to storage width. The catalog's 113 eligible
constants are classified as satisfying the parameter domain. This does not
claim 113 separately proved check-value equalities, nor does it discharge
partial-width constructor coherence. The coverage JSON expressly states both
limitations. The finite supported-instance denominator excludes arbitrary
custom implementations and unsealed const-lane families, as required.

README domain wording agrees with these restrictions and points to exact
constructor/protocol domains. One clarity suggestion was sent to root: describe
generated Lean as never hand-edited, rather than saying generated bodies remain
unchanged in a way that could imply frontend normalization produces identical
code to the unnormalized extraction. The accepted claim is source computations
preserved modulo the reviewed type/display-name normalization.

## Universal-width constructors and closed computation chains

Reviewed `PartialNoTableConstructors` and the final direct-construction versions
of `PartialConstructor8/16/32/64/128`. This supersedes the earlier full-width-only
constructor limitation: all ten NoTable/Table<1> constructor mappings now refer
to valid-width theorems. The accepted-build decision still belongs to final
owner/clean verification evidence.

For each storage type, `PartialNoTableConstructors.new_totalN` proves success
of the actual generated `new 0` for 1<=width<=N and preserves the algorithm.
There is no polynomial/init/xorout bound for this constructor-only result.
The table helper is related by an explicit equality to actual polynomial
initialization followed by its original zero-lane loop. Its loop proof preserves
the empty table. This handles source operations that execute even when no table
entries exist; it does not replace the constructor by an abstract empty record.

The five `checksumN` statements require bounded polynomial and xorout, but now
allow arbitrary raw algorithm init and explicitly use its low-w projection.
In particular checksum8 and checksum16 remove the earlier direct-checksum
bounded-init restriction. `new_checksumN` uses the actual constructor-success
witness, algorithm equality and actual checksum theorem to establish the full
new→checksum chain, with arbitrary slices and both flags. No cache-coherence
assumption is introduced for NoTable.

Each `PartialConstructorN.new_table1` establishes actual constructor success,
algorithm preservation and canonical current-table coherence for every valid
width with bounded polynomial; init/xorout/refout do not need extra bounds for
construction itself. Its proof runs the original generated table loop, whose
prefix invariant covers all 256 byte indices, and connects its entries to the
independent width-w transition via encoding/reflection lemmas.

The inspected 64-bit final file uses `table_prepared`, an equality of the actual
generated table helper to the same initialization-plus-original-loop fragment.
It no longer uses a synthetic constructor detour. `Partial64.withPoly` remains
only a mathematical transport object for the existing table's aligned physical
polynomial. Actual computation theorems retain the original self/algorithm and
source calls, with explicit canonical encoding equalities; no generated source
body or input algorithm is replaced in the public conclusion.

New→checksum closure is explicit in the inspected constructor modules. The
32/128 modules additionally expose actual digest-with-custom-initial→update→
finalize protocol and new→protocol roots; 8/16 expose corresponding protocol
composition. Each consumes constructor-established coherence rather than
assuming it for the newly constructed object. Custom initial values use low-w
projection. Protocol coverage remains tied to the named theorem inventory;
a constructor plus a pure mathematical law alone is not counted as an extra
public method or claimed as a separately proved protocol root.

The updated mapping snapshot has 75 distinct stage2 public instances and 96/171
combined instances. All five Table<1> constructor rows specify valid width and
bounded current polynomial, and all five NoTable constructor rows specify only
valid width. The stronger NoTable checksum rows describe arbitrary initial
words via low-w projection. This count increase includes the newly covered
NoTable u64/u128 constructors; strengthening existing constructor/checksum
domains is not double-counted as additional APIs. Earlier 94/171 and
full-width-constructor text above describes historical review snapshots only.
