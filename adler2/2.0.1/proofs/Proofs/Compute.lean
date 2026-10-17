module
public import Proofs.SplitPrelude
public import Proofs.FinalCombine
public import Proofs.FourChunks
public import Proofs.RawBridge
public import Proofs.FinalTail

@[expose] public section
open Aeneas.Std Aeneas.Std.WP
namespace adler2

private theorem chunk_size_ok :
    algo.Adler32.compute.CHUNK_SIZE = .ok 22208#usize := by
  have hmax : (5552#usize).val * (4#usize).val ≤ Usize.max := by
    scalar_tac
  obtain ⟨z,hz,hval⟩ :=
    spec_result_ok (Usize.mul_spec (x := 5552#usize) (y := 4#usize) hmax)
  have hzeq : z = 22208#usize :=
    UScalar.val_eq_imp _ _ (by simpa using hval)
  simpa [algo.Adler32.compute.CHUNK_SIZE, hzeq] using hz

private theorem zero_lane :
    laneValues (Array.repeat 4#usize 0#u32 : algo.U32X4) = (fun _ => 0) := by
  funext i
  fin_cases i <;> simp [laneValues, Array.repeat]

private theorem from_u16_val (x : U16) :
    (core.convert.num.FromU32U16.from x).val = x.val := by
  exact core.convert.num.FromU32U16.from_val_eq x

private def computeAfterSplit (a b : U32) (pre tail : Slice U8) :
    Result Adler32 := do
  let a1 := Array.repeat 4#usize 0#u32
  let i4 ← algo.Adler32.compute.CHUNK_SIZE
  let chunk_iter ← core.slice.Slice.chunks_exact pre i4
  let remainder_chunk ← core.slice.iter.ChunksExact.getRemainder chunk_iter
  let (b1, a_vec, b_vec) ← algo.Adler32.compute_loop0 i4 chunk_iter a b a1 a1
  let iter ← core.slice.Slice.chunks_exact remainder_chunk 4#usize
  let (a_vec1, b_vec1) ← algo.Adler32.compute_loop1 iter a_vec b_vec
  let i5 := Slice.len remainder_chunk
  let i6 ← lift (UScalar.cast .U32 i5)
  let i7 ← i6 * a
  let b2 ← b1 + i7
  let a_vec2 ←
    algo.U32X4.Insts.CoreOpsArithRemAssignU32.rem_assign a_vec1
      algo.Adler32.compute.MOD
  let b_vec2 ←
    algo.U32X4.Insts.CoreOpsArithRemAssignU32.rem_assign b_vec1
      algo.Adler32.compute.MOD
  let b3 ← b2 % algo.Adler32.compute.MOD
  let (a5, b4) ← finalCombine a b3 a_vec2 b_vec2
  let iter3 ← core.slice.Slice.iter tail
  let (a6, b5) ← algo.Adler32.compute_loop4 iter3 a5 b4
  let i22 ← a6 % algo.Adler32.compute.MOD
  let i23 ← lift (UScalar.cast .U16 i22)
  let i24 ← b5 % algo.Adler32.compute.MOD
  let i25 ← lift (UScalar.cast .U16 i24)
  .ok { a := i23, b := i25 }

private theorem compute_decompose (s : Adler32) (bytes : Slice U8) :
    algo.Adler32.compute s bytes =
      (do
        let a ← lift (core.convert.num.FromU32U16.from s.a)
        let b ← lift (core.convert.num.FromU32U16.from s.b)
        let (pre,tail) ← split4Prelude bytes
        computeAfterSplit a b pre tail) := by
  simp [algo.Adler32.compute, split4Prelude, computeAfterSplit,
    finalCombine, correctLanes]

private theorem computeAfterSplit_spec (a b : U32)
    (pre tail : Slice U8)
    (ha : a.val ≤ 65535) (hb : b.val ≤ 65535)
    (hpre : pre.val.length % 4 = 0)
    (htail : tail.val.length < 4) :
    ∃ out : Adler32, computeAfterSplit a b pre tail = .ok out ∧
      observe out = run (a.val,b.val) (pre.val ++ tail.val) := by
  obtain ⟨chunkIter,hchunks,hchunkSize,hremLen,hpartition⟩ :=
    sliceChunksExact_partition pre 22208#usize (by decide)
  have hchunkSize' : ∀ c ∈ chunkIter.chunks, c.val.length = 22208 := by
    simpa using hchunkSize
  have hremShort : chunkIter.remainder.val.length < 22208 := by
    simpa using hremLen
  have hremDiv : chunkIter.remainder.val.length % 4 = 0 :=
    remainder_chunk_multiple4 pre chunkIter hchunkSize' hpartition hpre
  let Z : algo.U32X4 := Array.repeat 4#usize 0#u32
  have hZero : laneValues Z = (fun _ => 0) := zero_lane
  let r0 := normalize (a.val,b.val)
  have hr0 := normalize_normalized (a.val,b.val)
  have hInv0 : laneInv a.val b.val r0.1 r0.2 (laneValues Z) (laneValues Z) := by
    simpa [r0, hZero, normalize] using
      laneInv_initial_normalized a.val b.val
  have hZBound : ∀ j : Fin 4, laneValues Z j < modulus := by
    intro j
    rw [congrFun hZero j]
    exact modulus_pos
  obtain ⟨b1,A,B,houter,hInvOuter,hb1,hA,hB⟩ :=
    compute_loop0_spec 22208#usize chunkIter a b Z Z r0.1 r0.2
      (by decide) hchunkSize' ha hb hZBound hZBound hr0.1 hr0.2 hInv0
  obtain ⟨iter4,hiter4,hsize4,hrem4,hcount4,hflat4⟩ :=
    sliceChunks4_short chunkIter.remainder hremDiv hremShort
  have hA0 : ∀ j : Fin 4, laneValues A j ≤ aBound 0 := by
    intro j
    have := hA j
    simp [aBound, modulus] at *
    omega
  have hB0 : ∀ j : Fin 4, 2 * laneValues B j ≤ bBound2 0 := by
    intro j
    have := hB j
    simp [bBound2, modulus] at *
    omega
  obtain ⟨A1,B1,hinner,hfold,hA1,hB1⟩ :=
    compute_loop1_spec iter4 A B 0 hsize4 (by omega) hA0 hB0
  let rFull := run r0 ((chunkIter.chunks.map Slice.val).flatten)
  have hrFull := run_normalized r0 ((chunkIter.chunks.map Slice.val).flatten)
  have hGroup :=
    laneInv_groups a.val b1.val rFull.1 rFull.2
      (laneValues A) (laneValues B) iter4.chunks hsize4 hInvOuter
      hrFull.1 hrFull.2
  have hcountExact : 4 * iter4.chunks.length =
      chunkIter.remainder.val.length := by
    have hflatLen := exact_chunks_flatten_length iter4.chunks 4 hsize4
    rw [hflat4] at hflatLen
    omega
  let rRem := run rFull chunkIter.remainder.val
  have hInvRaw : laneInv a.val
      (b1.val + chunkIter.remainder.val.length * a.val)
      rRem.1 rRem.2 (laneValues A1) (laneValues B1) := by
    have hnum : 4 * a.val * iter4.chunks.length =
        chunkIter.remainder.val.length * a.val := by
      rw [← hcountExact]
      ring
    have hFA := congrArg Prod.fst hfold
    have hFB := congrArg Prod.snd hfold
    simpa only [hnum, hflat4, ← hFA, ← hFB] using hGroup
  have hcast : (UScalar.cast .U32 (Slice.len chunkIter.remainder)).val =
      chunkIter.remainder.val.length := by
    rw [UScalar.cast_val_eq, Slice.len_val]
    have hbits : 2 ^ UScalarTy.U32.numBits = 4294967296 := by decide
    rw [hbits]
    have hlt : chunkIter.remainder.val.length < 4294967296 :=
      Nat.lt_trans hremShort (by decide)
    exact Nat.mod_eq_of_lt hlt
  have hrawMulBound : chunkIter.remainder.val.length * a.val ≤
      22207 * 65535 := by
    calc
      _ ≤ 22207 * a.val := Nat.mul_le_mul_right a.val (by omega)
      _ ≤ 22207 * 65535 := Nat.mul_le_mul_left 22207 ha
  have hmulSafety :
      (UScalar.cast .U32 (Slice.len chunkIter.remainder)).val * a.val <
        4294967296 := by
    rw [hcast]
    omega
  obtain ⟨i7,hi7,hi7val⟩ :=
    u32_mul_ok (UScalar.cast .U32 (Slice.len chunkIter.remainder))
      a hmulSafety
  have haddSafety : b1.val + i7.val < 4294967296 := by
    rw [hi7val, hcast]
    omega
  obtain ⟨b2,hb2,hb2val⟩ := u32_add_ok b1 i7 haddSafety
  have hmod : algo.Adler32.compute.MOD.val = modulus := by
    norm_num [algo.Adler32.compute.MOD, modulus]
  have hmodnz : algo.Adler32.compute.MOD.val ≠ 0 := by
    rw [hmod]
    decide
  obtain ⟨A2,hA2,hA2val⟩ :=
    spec_result_ok (u32x4_rem_assign_spec A1 algo.Adler32.compute.MOD hmodnz)
  obtain ⟨B2,hB2,hB2val⟩ :=
    spec_result_ok (u32x4_rem_assign_spec B1 algo.Adler32.compute.MOD hmodnz)
  obtain ⟨b3,hb3,hb3val⟩ :=
    u32_rem_ok b2 algo.Adler32.compute.MOD hmodnz
  have hAMod : laneValues A2 = laneMod (laneValues A1) := by
    funext j
    have h := hA2val j
    change laneValues A2 j = _ at h
    rw [h, hmod]
    rfl
  have hBMod : laneValues B2 = laneMod (laneValues B1) := by
    funext j
    have h := hB2val j
    change laneValues B2 j = _ at h
    rw [h, hmod]
    rfl
  have hb3val : b3.val =
      (b1.val + chunkIter.remainder.val.length * a.val) % modulus := by
    rw [hb3val, hmod, hb2val, hi7val, hcast]
  have hInvFinal : laneInv a.val b3.val rRem.1 rRem.2
      (laneValues A2) (laneValues B2) := by
    simpa only [hb3val, hAMod, hBMod] using
      laneInv_mod a.val
        (b1.val + chunkIter.remainder.val.length * a.val)
        rRem.1 rRem.2 (laneValues A1) (laneValues B1) hInvRaw
  have hrRem := run_normalized rFull chunkIter.remainder.val
  have hb3Small : b3.val < modulus := by
    rw [hb3val]
    exact Nat.mod_lt _ modulus_pos
  have hA2Small : ∀ j : Fin 4, laneValues A2 j < modulus := by
    intro j
    rw [hAMod]
    exact Nat.mod_lt _ modulus_pos
  have hB2Small : ∀ j : Fin 4, laneValues B2 j < modulus := by
    intro j
    rw [hBMod]
    exact Nat.mod_lt _ modulus_pos
  obtain ⟨a5,b4,hcombine,ha5mod,hb4mod,ha5bound,hb4bound⟩ :=
    finalCombine_laneInv a b3 A2 B2 rRem.1 rRem.2
      ha hb3Small hA2Small hB2Small hInvFinal hrRem.1 hrRem.2
  obtain ⟨out,htailResult,hobsTail⟩ :=
    finalTail_spec a5 b4 tail ha5bound hb4bound (by omega)
  have hObsPrefix :
      run (a.val,b.val) pre.val = rRem := by
    rw [← hpartition, run_append]
    simp only [rRem, rFull, r0]
    rw [run_normalize_seed]
  have hObsAll :
      run (a.val,b.val) (pre.val ++ tail.val) = run rRem tail.val := by
    rw [run_append, hObsPrefix]
  have hobs : observe out =
      run (a.val,b.val) (pre.val ++ tail.val) := by
    rw [hobsTail]
    rw [run_of_mod a5.val b4.val rRem.1 rRem.2 tail.val
      ha5mod hb4mod hrRem.1 hrRem.2]
    exact hObsAll.symm
  refine ⟨out, ?_, hobs⟩
  simp only [Z] at houter
  simp [computeAfterSplit, chunk_size_ok, hchunks,
    chunksExact_getRemainder, houter, hiter4, hinner,
    hi7, hb2, hA2, hB2, hb3, hcombine, lift]
  simpa only [finalTail, lift, bind_ok] using htailResult

theorem compute_spec (s : Adler32) (bytes : Slice U8) :
    ∃ out : Adler32,
      algo.Adler32.compute s bytes = .ok out ∧
      observe out = run (observe s) bytes.val := by
  obtain ⟨pre,tail,hsplit,hpart,hpre,_,htail⟩ :=
    split4Prelude_spec bytes
  let a : U32 := core.convert.num.FromU32U16.from s.a
  let b : U32 := core.convert.num.FromU32U16.from s.b
  have ha : a.val ≤ 65535 := by
    rw [from_u16_val]
    scalar_tac
  have hb : b.val ≤ 65535 := by
    rw [from_u16_val]
    scalar_tac
  obtain ⟨out,hcore,hobs⟩ :=
    computeAfterSplit_spec a b pre tail ha hb hpre htail
  refine ⟨out, ?_, ?_⟩
  · rw [compute_decompose]
    simpa [a, b, lift, hsplit] using hcore
  · rw [hobs, hpart]
    simp [a, b, observe]

end adler2
