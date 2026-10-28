# Independent review of the fixed-width standard model boundary

Review scope: `proofs/IntegerFixedDirect/FunsExternal.lean`, generated `Funs.lean` and `Types.lean`, and their actual standard primitive instantiations. This is a semantic review of an explicit trusted supplement, not a machine-checked compiler or Rust standard-library correctness proof. No upstream function, generated function body, compiler binary or LLBC normalization was introduced by this review.

## Authoritative material actually read

- [Rust size_of documentation](https://doc.rust-lang.org/std/mem/fn.size_of.html): primitive integer byte sizes, pointer-sized types, and general layout distinction.
- [Rust slice clone_from_slice documentation](https://doc.rust-lang.org/std/primitive.slice.html#method.clone_from_slice): equal-length copying and panic on unequal lengths.
- [Rust usize byte conversion documentation](https://doc.rust-lang.org/std/primitive.usize.html#method.to_le_bytes): pointer-sized endian conversion.
- The installed extraction toolchain's actual source, rooted at `/workspace/.rustup/toolchains/nightly-2026-09-17-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/`: `mem/mod.rs` primitive-size table and size_of at line375; `slice/mod.rs` clone_from_slice at4275 and trivial-clone specialization at5638; `num/uint_macros.rs` to_le_bytes at4041/from_le_bytes at4138 and adjacent to_be_bytes; `num/int_macros.rs` corresponding signed methods at3782/3879. These local sources fix the extraction version even though online stable documentation can advance.

## size_of: selected builtin scalar domain only

The supplement chooses byte counts using Nat.card of the Lean type. This is an implementation device for selected scalar domains, not a model of Rust layout for arbitrary finite types. Rust can pad types or have invalid bit patterns; cardinality is not a general layout formula. The reviewed domain is U8/U16/U32/U64/I8/I16/I32/I64 and Usize/Isize under the extracted target assumption. On those domains the scalar cardinalities select exactly 1/2/4/8 bytes, agreeing with Rust primitive sizes.

Inspection of generated Funs.lean finds exactly twenty size_of calls: two each for the ten builtin scalar types, in their encode/decode wrappers. There is no generic application type at these sites. Thus this is a primitive-domain restriction, not a condition on integer-encoding's desired result. Arbitrary other calls to this polymorphically typed definition are outside the reviewed boundary even if their cardinality happens to match.

The proof package should establish the concrete size reductions and carry the target assumption where needed; the definition's transparency and absence of custom axioms alone do not establish its Rust adequacy.

## clone_from_slice: standard byte cloning only

There are exactly ten generated calls, all instantiated with U8 and `core.clone.CloneU8`. Actual nightly Rust delegates to slice cloning and specializes trivial cloning to copying; unequal lengths panic. The supplement returns source byte contents as the updated destination exactly when lengths agree, otherwise panic. In Aeneas's value model this represents the mutation result; it does not claim to replace allocation identity or clone arbitrary objects.

The ignored Clone dictionary is adequate only for the standard U8 dictionary actually passed at every site. It is not adequate for an arbitrary dictionary merely having the same Lean type: a custom dictionary could change values, fail or have effects. Nor is the fallback panic an accurate model of all other Rust Clone types. Both are excluded domains. The U8/equal-length behavior is reusable standard slice semantics, independent of the caller's encoding algorithm.

## Six pointer-sized conversion aliases

Usize/Isize to_le_bytes, to_be_bytes and from_le_bytes delegate through the corresponding 64-bit Aeneas primitive and bitvector width conversion. For the extracted x86_64 target and `Platform.numBits = 64`, width conversion preserves all bits and the aliases implement the standard pointer-sized endian methods, including signed two's-complement patterns. Rust's actual macro definitions use endian conversion plus native byte representation; they do not generally truncate values to64 or have a fixed eight-byte result on every platform.

Every public pointer-sized theorem using these aliases must therefore require `Platform.numBits = 64`, including light encoding and byte reversal, not just wrappers that call size_of. No portable 32-bit or arbitrary-platform claim follows. Endian functions must ultimately be connected to independent positional bytes from SPEC.md; alias equality or an encode/decode roundtrip alone is too weak.

## Acceptance and remaining evidence requirements

The supplement is acceptable within the enumerated standard primitive domains. It contains no application-specific encoding result, input value restriction chosen to force a result, or replacement implementation of FixedInt. Actual upstream control flow and calls remain the theorem subject. The trusted boundary includes the usual Rust-to-LLBC/Aeneas translation, scalar representation and existing standard models, plus these explicitly reviewed supplements. It does not establish compiler correctness, arbitrary Rust layout, arbitrary Clone, allocation or I/O correctness.

Root's regeneration/source checks must retain unchanged generated bodies and the exact supplemental file; theorem audits must reject extra axioms and roots must expose all preconditions. This review inspected the calls and definitions; successful proof compilation and artifact equality are separate validation evidence owned by root/proof agents.

## Independent native finding classification

Reviewed `native-findings.md`: three separately grouped observations are justified, with the qualifications already recorded. IE-S1 is target-specific byte capacity and partial consumption, including reading one extra byte before rejection. IE-S2 is checked numeric rejection mapped to UnexpectedEof despite a complete prefix; no external contract mandates one specific replacement error kind. IE-G1 is the undocumented eight-byte capacity of generic FixedInt adapters, demonstrated with a correctly implemented sixteen-byte integer. Read/write or sync/async manifestations do not multiply these root causes; async is source review only.

Oversized fixed-slice rejection is a documentation omission/ambiguity rather than an unequivocal promise violation. Short varint encode buffers violate an explicit precondition and are not defects. A restricted-domain custom FixedInt whose decoder returns None could trigger the reader's unwrap; because the trait's intended admissible bit-pattern law is unclear, this is a conditional limitation, not an additional confirmed finding. No external report was made.

## Selected unwrap formatting-dictionary erasure

A later transitive audit found the pre-existing Aeneas Formatter type axiom in fixed decode roots, reached through the standard Debug dictionary type despite no formatting operation being evaluated by the model. Inspected actual installed `adler2/2.0.1/.tools/aeneas/backends/lean/Aeneas/Std/Core/Fmt.lean`: Formatter is an axiom at line15; Result.unwrap at line23 ignores its Debug argument and returns Ok's payload or panic for Err. Inspected actual extraction-nightly `core/src/result.rs` unwrap at1226 and unwrap_failed at1869: Rust returns the payload on Ok and panics on Err, with error formatting in the panic path. The selected standard TryFromSliceError is declared in core/src/array/mod.rs; this is not a user-defined Debug callback.

The local supplement replaces that formatting-only dictionary with Unit for exactly TryFromSliceError and defines unwrap with the identical existing Aeneas Ok/Err match. All ten generated fixed decode call sites pass this exact standard error dictionary. No source or generated body was edited. This restricted dictionary erasure is semantically acceptable in the existing Aeneas Result observation model, which does not retain panic text, formatter state, panic hooks or unwind effects. It does not claim arbitrary Rust Debug effects can be erased, nor does it change an Err into success. Public decode success also establishes that the array conversion actually returns Ok on the branch that reaches unwrap.

This is an additional explicit standard-model binding boundary, not a proof that Rust's formatting implementation has no effects and not a blanket exception to the axiom audit. Root must re-audit the final roots and retain the exact shim plus the ten-call census; accepted dependencies should no longer include Formatter. The underlying compiler/backend files remain unchanged.
