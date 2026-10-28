# Independent review of Vec helper contracts

This review concerns the actual generated trait-default bodies in IntegerVec.lean and IntegerFixedVec.lean and their public scalar specializations in VarintVec.lean and FixedVec.lean. It distinguishes a proved conditional generic lemma from a public scalar result with those conditions discharged. Proof compilation/audits are separate retained evidence; this semantic review does not replace them.

## Actual source and dictionary dependencies

The unchanged source VarInt::encode_var_vec allocates a zero-filled vector of required_space, passes its mutable slice to encode_var, and returns the vector. The extracted default body executes exactly those steps and uses exactly the required_space and encode_var dictionary fields. It does not execute decode_var, the dictionary's encode_var_vec field, or the Copy marker. All ten built-in source implementations inherit this default and bind the two executed fields to their corresponding actual scalar methods.

The unchanged FixedInt::encode_fixed_vec invokes encode_fixed_light, calls AsRef<[u8]> on its associated Bytes result, then copies that slice into a vector. The extracted default body executes those operations and reads only encode_fixed_light and coreconvertAsRefSelf_BytesSliceU8Inst. Built-in source implementations set Bytes to [u8;size_of::<Self>()], use their actual to_le_bytes-based light method, and inherit the default Vec method. The associated array uses standard array-to-slice AsRef. FixedVec.specialize explicitly supplies those two fields. None of encode_fixed, decode_fixed, switch_endianness, the self Vec method, the Copy marker or ENCODED_SIZE is executed.

Consequently universally quantifying the other dictionary fields is sound: their values cannot affect this body's evaluation. This is stronger than requiring an arbitrary filler implementation to behave correctly, and it introduces no assumed application law. The theorem remains about a specialization of the actual extracted generic body, not a separately generated full concrete Rust dictionary. Connecting it to each builtin public instance includes a structural source/dictionary correspondence boundary: the inherited default and its executed field bindings must match the source impl. This was checked in fixed.rs's impl_fixedint macro and all ten invocations, and varint.rs's eight macro invocations plus explicit u64/i64 impls. Future overrides or different bindings would require renewed review.

Fixed-Vec extraction excludes only the unused default ENCODED_SIZE declaration from its configuration; the trait field is retained in IntegerFixedVec.lean and the executable body never reads it. Excluding that metadata does not remove a runtime check or operation from this default. It must not be generalized to dropping executed associated constants.

## Required semantic strength

VarintVec.EncodedVec states exact length uLen(u) and every arithmetic base-128 byte, including continuation bits. Together these determine the complete vector, so this is canonical encoding, not a roundtrip-only result. The generic_total hypotheses require actual required-space success and actual encode-var success with the full encoding contract on adequate buffers. Public scalar roots must discharge them using the extracted scalar methods; the generic lemma alone earns no public scalar coverage. Signed instances must set u to the mathematical ZigZag of the signed value, including minimum/maximum values, rather than its raw two's-complement natural residue.

FixedVec roots compare the entire output's byte values with fixedBytes(m,x.bv.toNat). This is the independent positional little-endian representation, with exact length. For signed scalars x.bv.toNat is the nonnegative residue of the two's-complement value and therefore includes both signed extrema correctly. Standard fixedBytes and endian bridges in FixedSpec establish arithmetic bytes, rather than just equality to a Rust/Aeneas endian primitive. Pointer roots must expose Platform.numBits=64, as in the standard-model review.

## Allocation and model boundary

Both proofs use existing Aeneas Std Vec/slice operations. They model mathematical vector contents and successful allocation; they do not prove real memory availability, allocator behavior, OOM recovery, capacity choices, allocation identity or execution cost. The Rust program may exhaust resources even when the value-model theorem succeeds. This applies equally to zero-fill allocation and slice-to-vector copying. No additional application axiom or alternative encoding algorithm is justified by that standard allocation idealization.

## Review snapshot and pending checks

At the initial inspection, FixedVec contained eight non-pointer scalar roots with exact fixedBytes conclusions; VarintVec contained the generic conditional lemma. Those statements were semantically adequate within the boundaries above. Final public coverage requires checking each subsequently added scalar specialization, especially signed ZigZag and pointer-width preconditions, and successful build/axiom audit. No absent scalar root is approved by this initial snapshot.

## Final concrete-specialization review

The completed files now contain all ten VarintVec scalar roots and all ten FixedVec scalar roots. Each VarintVec sourceDictionary binds required_space and encode_var directly to that scalar's extracted methods and the standard Copy instance; only unused decode_var and encode_var_vec are universal arbitrary functions. Each public root discharges both generic semantic premises using proved actual-method contracts. Unsigned output uses value.val; all five signed outputs use mathematical zigzag(value.val), with no exclusion of extrema. Therefore these are exact canonical-byte roots for every representable input, under the stated value/allocation model.

All ten FixedVec roots bind the extracted light method and standard array AsRef; eight fixed-size scalars have no extra numerical restriction, and usize/isize explicitly require System.Platform.numBits=64. The pointer-sized VarintVec roots do not use the fixed eight-byte aliases; they compose the actual scalar-cast/varint contracts and do not inherit that additional fixed-conversion precondition. The extraction target remains recorded independently.

Source-default inheritance and executed-field correspondence are adequate for mapping these twenty roots to the builtin public helpers within the structural specialization boundary above. They do not prove arbitrary custom dictionaries correct, and do not depend on assumptions that an unused callback succeeds. Sol reports successful builds and permitted-axiom audits; root's fresh verification remains the authoritative execution evidence. This final review supersedes the initial pending-specialization snapshot, without asserting real-resource allocation success.
