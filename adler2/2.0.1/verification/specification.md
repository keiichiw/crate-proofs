# Mathematical contract for adler2 2.0.1

Designed by the Astra specification subagent from the pinned, unchanged
`upstream/src/lib.rs` and `upstream/src/algo.rs`. This document states proof
obligations; it is not evidence that the obligations have been discharged.
Sol owns Lean implementation and execution. Results and audited theorem names
must be reported separately in `results.md`.

## State and observations

The selected type is `adler2.Adler32`, whose source is `upstream/src/lib.rs`,
not the disambiguated sysroot dependency `adler2.adler2_1.Adler32`.
An arbitrary state consists of two U16 values, each in 0 through 65535.
`from_checksum` accepts every U32, so normalized halves cannot be assumed.
The arithmetic encoding is `65536 * b + a`; decoding is
`a = checksum % 65536`, `b = checksum / 65536`.
Encoding and decoding do not reduce modulo 65521.

The initial milestone obligations below are exact Lean proposition shapes
using the existing generated declarations and `open Aeneas.Std` inside
`namespace adler2`. The proposed names can change, but their quantifiers and
postconditions must remain intact.

```lean
-- checksum_spec
∀ s : Adler32, ∃ out : U32,
  Adler32.checksum s = Result.ok out ∧
  out.val = s.b.val * 65536 + s.a.val

-- from_checksum_spec
∀ checksum : U32, ∃ out : Adler32,
  Adler32.from_checksum checksum = Result.ok out ∧
  out.a.val = checksum.val % 65536 ∧
  out.b.val = checksum.val / 65536

-- checksum_from_checksum
∀ checksum : U32,
  (do let s ← Adler32.from_checksum checksum
      Adler32.checksum s) = Result.ok checksum

-- from_checksum_checksum
∀ s : Adler32,
  (do let checksum ← Adler32.checksum s
      Adler32.from_checksum checksum) = Result.ok s
```

These are total-success properties, not conditional implications from successful
execution. They cover all bit patterns, including `0xffffffff`, without finite
enumeration or a normalized-seed hypothesis.

## Scalar specification for updates

Use natural-number state pairs and byte values. The following definitions are
independent of the optimized implementation:

```lean
def modulus : Nat := 65521

def normalize (s : Nat × Nat) : Nat × Nat :=
  (s.1 % modulus, s.2 % modulus)

def step (s : Nat × Nat) (byte : U8) : Nat × Nat :=
  let a := (s.1 + byte.val) % modulus
  (a, (s.2 + a) % modulus)

def run (s : Nat × Nat) (bytes : List U8) : Nat × Nat :=
  bytes.foldl step (normalize s)

def observe (s : Adler32) : Nat × Nat := (s.a.val, s.b.val)

def encode (s : Nat × Nat) : Nat := s.2 * 65536 + s.1
```

Normalizing before the fold is intentional. The release normalizes even an
empty update, so `run s [] = normalize s`. A fold initialized with the raw state
would incorrectly promise an unchanged state on empty input. For example,
`from_checksum 0xffffffff` has halves `(65535,65535)`; an empty update yields
`(14,14)`, hence checksum `0x000e000e`.

The clean extraction exposes the actual update functions below. Their required
functional contracts use these extracted names and argument order:

```lean
-- compute_spec
∀ (s : Adler32) (bytes : Slice U8), ∃ out : Adler32,
  algo.Adler32.compute s bytes = Result.ok out ∧
  observe out = run (observe s) bytes.val

-- write_slice_spec
∀ (s : Adler32) (bytes : Slice U8), ∃ out : Adler32,
  Adler32.write_slice s bytes = Result.ok out ∧
  observe out = run (observe s) bytes.val

-- adler32_slice_spec
∀ bytes : Slice U8, ∃ out : U32,
  adler32_slice bytes = Result.ok out ∧
  out.val = encode (run (1, 0) bytes.val)

-- run_normalized
∀ (s : Nat × Nat) (bytes : List U8),
  (run s bytes).1 < modulus ∧ (run s bytes).2 < modulus

-- run_append
∀ (s : Nat × Nat) (xs ys : List U8),
  run s (xs ++ ys) = run (run s xs) ys
```

The extraction and proof must include actual optimized bodies and their helper
calls. A theorem about only `run`, or a theorem assuming correctness of those
bodies, does not discharge `compute_spec`. There is no input-length restriction
beyond the generated slice representation. The success equality includes
arithmetic/index safety and termination in the extracted model.

Derived obligations: every update produces normalized halves; empty updates
normalize raw states; updates over concatenated byte lists agree with successive
updates; checksum/decode between successive updates preserves the full state.
A monadic resumption theorem should use the actual constructors, observer, and
update, and derive its result from their checked contracts.

## Actual split-versus-whole and resumption contracts

The requested API law quantifies arbitrary initial states and all representable
whole slices, including empty parts. Its total-success form is:

```lean
-- write_slice_append_spec
∀ (s : Adler32) (xs ys whole : Slice U8),
  whole.val = xs.val ++ ys.val →
  ∃ out : Adler32,
    Adler32.write_slice s whole = Result.ok out ∧
    (do let mid ← Adler32.write_slice s xs
        Adler32.write_slice mid ys) = Result.ok out
```

The explicit `whole` slice records representability of concatenation. Two slices
can each fit `usize` while their combined length cannot. Equivalently a helper
may construct `whole` using the condition
`xs.val.length + ys.val.length ≤ Usize.max`. No additional byte-count limit or
normalized-state hypothesis is permitted. Equality of two `Result`s alone is
weaker than the stated success contract and must not replace it.

A corresponding resumption contract must insert the actual checksum and seed
constructor between updates, with the same exact state result:

```lean
-- write_slice_resume_spec
∀ (s : Adler32) (xs ys whole : Slice U8),
  whole.val = xs.val ++ ys.val →
  ∃ out : Adler32,
    Adler32.write_slice s whole = Result.ok out ∧
    (do let mid ← Adler32.write_slice s xs
        let checksum ← Adler32.checksum mid
        let restored ← Adler32.from_checksum checksum
        Adler32.write_slice restored ys) = Result.ok out
```

The existing state roundtrip and checked `compute_spec`/`write_slice_spec`,
together with scalar `run_append`, should derive these actual API laws. A theorem
about scalar `run` alone does not discharge either law. The extracted standalone
`adler32_slice` contract then gives whole-input checksum agreement from `(1,0)`.

## Four-lane correspondence and overflow invariants

Write `p = 65521`, initial halves `a0,b0 ≤ 65535`, and full groups of four
bytes as `x[t,j]` for zero-based lane `j ∈ {0,1,2,3}`. After `m` groups, let
`A[j]` be the lane byte sum and `B[j]` its running sum. Maintain congruences

- `A[j] ≡ Σ(t < m) x[t,j] (mod p)`;
- `B[j] ≡ Σ(t < m) (m - t) * x[t,j] (mod p)`;
- the separate scalar `b ≡ b0 + 4*m*a0 (mod p)` at chunk boundaries.

The main scalar `a` remains the original `a0` until combination. Lane residues
persist across chunks, so weighted sums are over the full processed prefix,
not independently reset chunk sums. In the current chunk, after `n ≤ 5552`
groups, previously reduced lanes satisfy

- `A[j] ≤ 65520 + 255*n ≤ 1481280`;
- `B[j] ≤ 65520 + n*65520 + 255*n*(n+1)/2 ≤ 4294690200`.

All are below `2^32`. The first chunk starts at zero, a stronger condition.
The scalar chunk contribution is safe even for an arbitrary public seed:
`b + 22208*a0 ≤ 65535 + 22208*65535 = 1455466815 < 2^32`.
Later scalar `b` is reduced below `p`. The final shorter chunk has at most
5551 groups and satisfies the same bounds.

After the final lane reductions, the implementation combines them with
`4*B[j] + j*(p-A[j])`. Because `A[j]<p`, the subtraction is safe and this is
congruent to `4*B[j] - j*A[j]` modulo `p`. Thus the combined state is congruent
to the scalar fold after `4*m` bytes:

- `a ≡ a0 + Σ(j < 4) A[j] (mod p)`;
- `b ≡ b0 + 4*m*a0 + Σ(j < 4) (4*B[j] - j*A[j]) (mod p)`.

Use integer congruence for the subtraction identity, or keep the nonnegative
`j*(p-A[j])` expression throughout the natural-number proof. Do not use
truncated natural subtraction to represent a potentially negative weighted sum.
Before the serial tail, conservative bounds are `a ≤ 327615` and
`b ≤ 1506966`. The tail has at most three bytes, giving `a ≤ 328380` and
`b ≤ 2491341`. Final reduction produces valid U16 values below `65521`.
These numerical bounds are proof obligations; this prose arithmetic does not
replace checked loop invariants and machine-operation safety lemmas.

### Cross-added lane invariant for checked implementation proofs

An equivalent local invariant avoids negative terms and global weighted sums.
Let the scalar reference after the processed full groups be `(ra,rb)`, let
`AΣ` and `BΣ` be sums of four accumulator lanes, and let
`W = A[1] + 2*A[2] + 3*A[3]`. With the scalar seed contribution `C`, maintain

- `ra ≡ a0 + AΣ (mod p)`;
- `rb + W ≡ C + 4*BΣ (mod p)`.

For each group `(x0,x1,x2,x3)`, the unreduced scalar recurrence is
`ra' = ra + x0+x1+x2+x3` and
`rb' = rb + 4*ra + 4*x0+3*x1+2*x2+x3` modulo `p`.
The lane recurrence `A'=A+x`, `B'=B+A'`, with ghost contribution
`C'=C+4*a0`, preserves the cross-added invariant by distributivity.
Within an inner loop, `C` is a ghost expression; the actual scalar accumulator
adds `4*n*a0` once at the chunk boundary. Reducing any lane modulo `p` preserves
the invariant. At final combination, normalized lanes satisfy
`Σ(j<4) j*(p-A[j]) + W = 6*p`; adding this equality to the invariant proves
the implemented nonnegative correction produces the scalar `rb` modulo `p`.
These are internal proof invariants, not additional assumptions on the program.

## Standard-library model partition prerequisites

The pinned Aeneas `Std/SliceIter.lean` implements `ChunksExact` using a concrete
list of slices and a stored remainder. `next` pops that list, and
`getRemainder` returns the stored remainder. `chunks_exact` constructs both via
`List.toChunksExact`. These are trusted standard-library models; checked lemmas
about their Lean definitions do not establish Rust/model equivalence.

The approved, implemented list-level prerequisite contracts are:

```lean
-- chunksExact_length
∀ {n : Nat} (hn : 0 < n) (l : List α),
  ∀ c ∈ (List.toChunksExact n hn l).1, c.length = n

-- chunksExact_remainder_lt
∀ {n : Nat} (hn : 0 < n) (l : List α),
  (List.toChunksExact n hn l).2.length < n

-- chunksExact_partition
∀ {n : Nat} (hn : 0 < n) (l : List α),
  (List.toChunksExact n hn l).1.flatten ++
    (List.toChunksExact n hn l).2 = l
```

The approved wrapper obligation connects those list properties to the actual
standard-library function called by the generated compute body:

```lean
-- sliceChunksExact_partition
∀ (s : Slice α) (n : Usize), 0 < n.val →
  ∃ iter : core.slice.iter.ChunksExact α,
    core.slice.Slice.chunks_exact s n = Result.ok iter ∧
    (∀ c ∈ iter.chunks, c.val.length = n.val) ∧
    iter.remainder.val.length < n.val ∧
    (iter.chunks.map (fun c => c.val)).flatten ++ iter.remainder.val = s.val
```

There is no minimum input length precondition; empty and shorter-than-chunk
inputs are included. Positivity is necessary because the model fails on a zero
chunk size. The remaining three finalized observation contracts are exact equations:

```lean
-- chunksExact_getRemainder
∀ iter : core.slice.iter.ChunksExact α,
  core.slice.iter.ChunksExact.getRemainder iter = Result.ok iter.remainder

-- chunksExact_next_cons
∀ (c : Slice α) (cs : List (Slice α)) (r : Slice α),
  core.slice.iter.IteratorChunksExact.next { chunks := c :: cs, remainder := r } =
    Result.ok (some c, { chunks := cs, remainder := r })

-- chunksExact_next_nil
∀ r : Slice α,
  core.slice.iter.IteratorChunksExact.next { chunks := [], remainder := r } =
    Result.ok (none, { chunks := [], remainder := r })
```

These preserve the stored remainder exactly; the nonempty transition consumes
exactly one complete slice, and the empty transition leaves the iterator empty.
None of these seven lemmas is a public adler2 API contract or the optimized-loop
correctness theorem.

## Extracted four-byte load helper

The finalized `u32x4_from_spec` contract applies to the actual extracted private
helper `algo.U32X4.from`, not a replacement mathematical implementation:

```lean
∀ (bytes : Slice U8), 4 ≤ bytes.val.length →
  ∃ out : algo.U32X4,
    algo.U32X4.from bytes = Result.ok out ∧
    out.val.map (fun x => x.val) = (bytes.val.take 4).map (fun x => x.val)
```

It proves successful in-bounds loading and exact unsigned widening of the first
four bytes, preserving lane order, for every slice of length at least four.
It covers the exact four-byte slices used by the optimized loop. Shorter slices
are outside this helper contract. This is an actual generated-body proof but
remains a private implementation prerequisite, not a public API coverage claim
or a proof of lane accumulation, combination, overflow bounds, or `compute`.

## Checked lane operations and scalar bridge scope

`Proofs/Spec.lean` defines the scalar specification above and proves normalization
idempotence, normalized output, and `run_append`. These mathematical results
include arbitrary natural-number seed pairs and empty lists.

`Proofs/AlgoOps.lean` states total-success WP contracts for the actual generated
private vector operations. For every lane `i : Fin 4`:

- `u32x4_rem_assign_spec` requires only nonzero divisor `q.val` and returns
  exactly `self[i].val % q.val`.
- `u32x4_add_assign_spec` requires each `self[i].val + other[i].val ≤ U32.max`
  and returns exactly that sum.
- `u32x4_mul_assign_spec` requires each `self[i].val * rhs.val ≤ U32.max`
  and returns exactly that product.

The WP here is total correctness, excluding failure and divergence. The checked
`spec_result_ok` bridge exposes its equivalent existential successful-result
shape for composing generated loop proofs. These private preconditions must be
discharged by the algorithm's loop invariants; they are not new public
preconditions on `compute`.

`Proofs/LaneMath.lean` uses `Lanes = Fin 4 → Nat`, explicit four-lane sums and
weights, and proves the cross-added invariant described above. `run_four`
expresses four scalar steps exactly for every natural seed pair. `laneInv_step`
preserves the modular relation across one lane update, `laneInv_mod` preserves
it across boundary reductions, and `laneInv_combine` proves the final corrected
sum when reference components and reduced A lanes are below the modulus.
The reference must be initialized with normalized seed components even when no
full group is processed; the actual machine seed remains the original U16
values. These arithmetic bridges alone do not establish that the Rust loops
maintain the invariant, terminate, or avoid overflow.

## Actual-loop and complete-core composition

The implementation contracts keep machine safety premises private:

- `compute_loop1_spec` and `compute_loop0_loop0_spec` return the exact four-lane
  fold of every pending four-byte chunk. Their bound is `k + chunkCount ≤ 5552`,
  with per-lane `A ≤ 65520 + 255*k` and
  `2*B ≤ 131040 + 131040*k + 255*k*(k+1)`. These count groups since the most
  recent reduction; they do not cap the complete input length.
- `compute_loop0_spec` admits an arbitrary number of full 22208-byte chunks.
  It preserves the lane invariant against the scalar `run` of their complete,
  ordered flattening, and reduces lane values after each full chunk. Its scalar
  input bound includes the raw U16 maximum 65535.
- `compute_loop2_spec` and `compute_loop3_spec` return exact sums of remaining
  iterator values. `compute_loop4_spec` returns the exact unreduced scalar fold
  on remaining tail bytes. Their bounds are discharged using the four reduced
  lanes and the final tail length below four.
- `finalCombine_generated` aligns the transparent correction/aggregation proof
  fragment with the generated operations. `finalTail_generated` does the same
  for the final byte loop, modulo operations, and U16 casts. The resulting exact
  observations are related to the scalar specification, rather than assuming
  correctness of a separately implemented checksum.

`compute_spec` composes these internal contracts with the actual generated
`algo.Adler32.compute` through a checked decomposition equality. The public
`write_slice_spec`, `adler32_slice_spec`, and split/resumption laws use this
proved theorem directly. They must expose no correctness hypothesis for
`compute`, no loop-bound premise, and no normalized-initial-state premise.
The scalar specification applies to all arbitrary public seeds, with empty
updates normalizing both halves as described above. The audit and execution
status of each named theorem belongs in `results.md`.

## Trust and scope

Lean proofs must have no `sorry`, custom axioms, application assumptions, or
hand-modified generated code. Audit every named public contract transitively;
only the repository's accepted standard axioms are allowed. The
Charon/Aeneas translation and standard-library model remain trusted boundaries.
Default-feature macOS arm64 extraction is the current target. Generic BufRead
IO, error behavior, derived traits, Hasher laws, no_std formal verification,
alternative platforms, and whole-crate correctness are outside this contract.
Native tests and source-identity checks are separate evidence. Local completion
does not imply successful cargo-proofs recording or publication.
