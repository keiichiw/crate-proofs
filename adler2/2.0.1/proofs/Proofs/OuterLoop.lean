module
public import Proofs.GroupBridge
public import Proofs.ComputeChunks
public import Proofs.LoopBridge
public import Proofs.FourChunks

@[expose] public section
open Aeneas.Std Aeneas.Std.WP
namespace adler2

theorem loop0_body_cons_numeric (chunk : Slice U8)
    (cs : List (Slice U8)) (r : Slice U8)
    (i : Usize) (a b : U32) (A B : algo.U32X4)
    (hiVal : i.val = 22208)
    (hsize : chunk.val.length = 22208)
    (ha : a.val ≤ 65535) (hb : b.val ≤ 65535)
    (hA : ∀ i : Fin 4, laneValues A i ≤ 65520)
    (hB : ∀ i : Fin 4, laneValues B i ≤ 65520) :
    ∃ (b' : U32) (A' B' : algo.U32X4) (groups : List (Slice U8)),
      algo.Adler32.compute_loop0.body
       i a {chunks := chunk :: cs, remainder := r} b A B =
       .ok (.cont ({chunks := cs, remainder := r}, b', A', B')) ∧
      b'.val = (b.val + 22208*a.val) % modulus ∧
      (∀ c ∈ groups, c.val.length = 4) ∧
      groups.length = 5552 ∧
      (groups.map Slice.val).flatten = chunk.val ∧
      laneValues A' = laneMod
        (groups.foldl (fun st c => laneStep st (chunkValues c))
          (laneValues A, laneValues B)).1 ∧
      laneValues B' = laneMod
        (groups.foldl (fun st c => laneStep st (chunkValues c))
          (laneValues A, laneValues B)).2 := by
  obtain ⟨iter2, hiter2, hiter2size, hrem, hcount, hpart⟩ :=
    sliceChunks4_full chunk hsize
  have hA0 : ∀ i : Fin 4, laneValues A i ≤ aBound 0 := by
    simpa [aBound] using hA
  have hB0 : ∀ i : Fin 4, 2 * laneValues B i ≤ bBound2 0 := by
    intro i
    have hb0 := hB i
    simp [bBound2]
    omega
  obtain ⟨A1,B1,hinner,hfold,hA1,hB1⟩ :=
    compute_loop0_loop0_spec iter2 A B 0
      hiter2size (by omega) hA0 hB0
  have hbody : algo.Adler32.compute_loop0.body i a
       {chunks := chunk :: cs, remainder := r} b A B =
      (do
        let iter2 ← core.slice.Slice.chunks_exact chunk 4#usize
        let (a_vec1, b_vec1) ← algo.Adler32.compute_loop0_loop0 iter2 A B
        let i1 ← lift (UScalar.cast .U32 i)
        let i2 ← i1 * a
        let b1 ← b + i2
        let a_vec2 ← algo.U32X4.Insts.CoreOpsArithRemAssignU32.rem_assign
          a_vec1 algo.Adler32.compute.MOD
        let b_vec2 ← algo.U32X4.Insts.CoreOpsArithRemAssignU32.rem_assign
          b_vec1 algo.Adler32.compute.MOD
        let b2 ← b1 % algo.Adler32.compute.MOD
        Result.ok (.cont ({chunks := cs, remainder := r}, b2, a_vec2, b_vec2))) := by
      simp [algo.Adler32.compute_loop0.body, chunksExact_next_cons]
  rw [hbody]
  rw [hiter2]
  simp only [bind_ok]
  rw [hinner]
  simp only [bind_ok, lift]
  have hcast : (UScalar.cast .U32 i).val = 22208 := by
    simp [UScalar.cast_val_eq, hiVal]
  have hmulSafety : (UScalar.cast .U32 i).val * a.val < 4294967296 := by
    rw [hcast]
    omega
  obtain ⟨i2, hi2, hi2val⟩ :=
    u32_mul_ok (UScalar.cast .U32 i) a hmulSafety
  have haddSafety : b.val + i2.val < 4294967296 := by
    rw [hi2val, hcast]
    omega
  obtain ⟨b1, hb1, hb1val⟩ := u32_add_ok b i2 haddSafety
  have hmod : algo.Adler32.compute.MOD.val = modulus := by
    norm_num [algo.Adler32.compute.MOD, modulus]
  have hmodnz : algo.Adler32.compute.MOD.val ≠ 0 := by
    rw [hmod]
    decide
  obtain ⟨A2, hA2, hA2val⟩ :=
    spec_result_ok (u32x4_rem_assign_spec A1 algo.Adler32.compute.MOD hmodnz)
  obtain ⟨B2, hB2, hB2val⟩ :=
    spec_result_ok (u32x4_rem_assign_spec B1 algo.Adler32.compute.MOD hmodnz)
  obtain ⟨b2, hb2, hb2val⟩ :=
    u32_rem_ok b1 algo.Adler32.compute.MOD hmodnz
  refine ⟨b2, A2, B2, iter2.chunks, ?_, ?_, hiter2size, hcount, hpart, ?_, ?_⟩
  · simp [hi2, hb1, hA2, hB2, hb2]
  · rw [hb2val, hmod, hb1val, hi2val, hcast]
  · funext j
    have h := hA2val j
    change laneValues A2 j = _ at h
    rw [h, hmod]
    have hf := congrArg Prod.fst hfold
    rw [← hf]
    rfl
  · funext j
    have h := hB2val j
    change laneValues B2 j = _ at h
    rw [h, hmod]
    have hf := congrArg Prod.snd hfold
    rw [← hf]
    rfl

theorem loop0_nil (i : Usize) (r : Slice U8) (a b : U32)
    (A B : algo.U32X4) :
    algo.Adler32.compute_loop0 i {chunks := [], remainder := r} a b A B =
      .ok (b, A, B) := by
  unfold algo.Adler32.compute_loop0
  rw [loop.eq_1]
  simp [algo.Adler32.compute_loop0.body,
    core.slice.iter.IteratorChunksExact.next]

theorem compute_loop0_spec (i : Usize)
    (iter : core.slice.iter.ChunksExact U8)
    (a b : U32) (A B : algo.U32X4) (ra rb : Nat)
    (hi : i.val = 22208)
    (hsize : ∀ chunk ∈ iter.chunks, chunk.val.length = 22208)
    (ha : a.val ≤ 65535) (hb : b.val ≤ 65535)
    (hA : ∀ j : Fin 4, laneValues A j < modulus)
    (hB : ∀ j : Fin 4, laneValues B j < modulus)
    (hra : ra < modulus) (hrb : rb < modulus)
    (hInv : laneInv a.val b.val ra rb (laneValues A) (laneValues B)) :
    ∃ b' A' B', algo.Adler32.compute_loop0 i iter a b A B =
        .ok (b', A', B') ∧
      let r := run (ra, rb) ((iter.chunks.map Slice.val).flatten)
      laneInv a.val b'.val r.1 r.2 (laneValues A') (laneValues B') ∧
      b'.val ≤ 65535 ∧
      (∀ j : Fin 4, laneValues A' j < modulus) ∧
      (∀ j : Fin 4, laneValues B' j < modulus) := by
  obtain ⟨chunks, rem⟩ := iter
  induction chunks generalizing b A B ra rb with
  | nil =>
      refine ⟨b, A, B, loop0_nil i rem a b A B, ?_⟩
      have hnorm : normalize (ra,rb) = (ra,rb) :=
        normalize_of_bounds _ hra hrb
      simpa [run, hnorm] using ⟨hInv, hb, hA, hB⟩
  | cons chunk cs ih =>
      have hchunk : chunk.val.length = 22208 := hsize chunk (by simp)
      have hcs : ∀ c ∈ cs, c.val.length = 22208 := by
        intro c hc
        exact hsize c (by simp [hc])
      have hA0 : ∀ j : Fin 4, laneValues A j ≤ 65520 := by
        intro j
        have := hA j
        simp only [modulus] at this
        omega
      have hB0 : ∀ j : Fin 4, laneValues B j ≤ 65520 := by
        intro j
        have := hB j
        simp only [modulus] at this
        omega
      obtain ⟨b1, A1, B1, groups, hbody, hb1, hgs, hgc, hgflat, hgA, hgB⟩ :=
        loop0_body_cons_numeric chunk cs rem i a b A B hi hchunk ha hb hA0 hB0
      have hgroup :=
        laneInv_groups a.val b.val ra rb (laneValues A) (laneValues B)
          groups hgs hInv hra hrb
      have hchunkRun : laneInv a.val (b.val + 22208 * a.val)
          (run (ra,rb) chunk.val).1 (run (ra,rb) chunk.val).2
          (groups.foldl (fun st c => laneStep st (chunkValues c))
            (laneValues A, laneValues B)).1
          (groups.foldl (fun st c => laneStep st (chunkValues c))
            (laneValues A, laneValues B)).2 := by
        have hnum : 4 * a.val * groups.length = 22208 * a.val := by
          rw [hgc]
          ring
        simpa only [hnum, hgflat] using hgroup
      have hmodInv := laneInv_mod a.val
        (b.val + 22208*a.val)
        (run (ra,rb) chunk.val).1 (run (ra,rb) chunk.val).2
        _ _ hchunkRun
      have hInv1 : laneInv a.val b1.val
          (run (ra,rb) chunk.val).1 (run (ra,rb) chunk.val).2
          (laneValues A1) (laneValues B1) := by
        simpa [hb1, hgA, hgB] using hmodInv
      have hb1Bound : b1.val ≤ 65535 := by
        rw [hb1]
        have hlt := Nat.mod_lt (b.val + 22208*a.val) modulus_pos
        have hm : modulus = 65521 := rfl
        omega
      have hA1Bound : ∀ j : Fin 4, laneValues A1 j < modulus := by
        intro j
        rw [hgA]
        exact Nat.mod_lt _ modulus_pos
      have hB1Bound : ∀ j : Fin 4, laneValues B1 j < modulus := by
        intro j
        rw [hgB]
        exact Nat.mod_lt _ modulus_pos
      have hr1 := run_normalized (ra,rb) chunk.val
      obtain ⟨b2, A2, B2, htail, hInvTail, hb2, hA2, hB2⟩ :=
        ih b1 A1 B1
          (run (ra,rb) chunk.val).1 (run (ra,rb) chunk.val).2
          hb1Bound hA1Bound hB1Bound hr1.1 hr1.2 hInv1 hcs
      refine ⟨b2,A2,B2, ?_, ?_, hb2,hA2,hB2⟩
      · unfold algo.Adler32.compute_loop0
        rw [loop.eq_1]
        simp only [hbody, bind_ok]
        exact htail
      · simpa only [List.map_cons, List.flatten_cons, run_append]
          using hInvTail

end adler2
