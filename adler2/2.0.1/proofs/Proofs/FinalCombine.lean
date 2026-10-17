module
public import Proofs.LaneLoop
public import Proofs.SumLoops

@[expose] public section

open Aeneas Aeneas.Std

namespace adler2

/-- The exact vector-correction fragment of the generated `compute` body. -/
def correctLanes (A B : algo.U32X4) : Result algo.U32X4 := do
  let b_vec3 ← algo.U32X4.Insts.CoreOpsArithMulAssignU32.mul_assign B 4#u32
  let i8 ← Array.index_usize A 1#usize
  let i9 ← algo.Adler32.compute.MOD - i8
  let i10 ← Array.index_usize b_vec3 1#usize
  let i11 ← i10 + i9
  let a2 ← Array.update b_vec3 1#usize i11
  let i12 ← Array.index_usize A 2#usize
  let i13 ← algo.Adler32.compute.MOD - i12
  let i14 ← i13 * 2#u32
  let i15 ← Array.index_usize a2 2#usize
  let i16 ← i15 + i14
  let a3 ← Array.update a2 2#usize i16
  let i17 ← Array.index_usize A 3#usize
  let i18 ← algo.Adler32.compute.MOD - i17
  let i19 ← i18 * 3#u32
  let i20 ← Array.index_usize a3 3#usize
  let i21 ← i20 + i19
  Array.update a3 3#usize i21

def correctedValues (a b : Lanes) : Lanes :=
  fun i => 4 * b i + i.val * (modulus - a i)

attribute [local step] u32x4_mul_assign_spec

theorem correctLanes_spec (A B : algo.U32X4)
    (hA : ∀ i : Fin 4, laneValues A i < modulus)
    (hB : ∀ i : Fin 4, laneValues B i < modulus) :
    correctLanes A B ⦃ out => laneValues out =
      correctedValues (laneValues A) (laneValues B) ⦄ := by
  have ha1 := hA 1
  have ha2 := hA 2
  have ha3 := hA 3
  have hb0 := hB 0
  have hb1 := hB 1
  have hb2 := hB 2
  have hb3 := hB 3
  unfold correctLanes
  step with u32x4_mul_assign_spec
  · intro i
    have hbi := hB i
    change laneValues B i * 4 ≤ U32.max
    simp only [modulus] at hbi
    rw [U32.max_eq]
    omega
  have hb01 := b_vec3_post 0
  have hb11 := b_vec3_post 1
  have hb21 := b_vec3_post 2
  have hb31 := b_vec3_post 3
  step* <;> simp_all [laneValues, modulus,
    algo.Adler32.compute.MOD, U32.max_eq] <;> try omega
  funext i
  fin_cases i <;> simp_all [laneValues, correctedValues, modulus] <;> omega

theorem array4_list (A : algo.U32X4) :
    A.val = [A.val[0], A.val[1], A.val[2], A.val[3]] := by
  have hlen : A.val.length = 4 := by simp
  have h0 : 0 < A.val.length := by omega
  have h1 : 1 < A.val.length := by omega
  have h2 : 2 < A.val.length := by omega
  have h3 : 3 < A.val.length := by omega
  have htake : A.val.take 4 =
      [A.val[0], A.val[1], A.val[2], A.val[3]] := by
    rw [List.take_succ_eq_append_getElem h3]
    rw [List.take_succ_eq_append_getElem h2]
    rw [List.take_succ_eq_append_getElem h1]
    rw [List.take_succ_eq_append_getElem h0]
    simp
  calc
    A.val = A.val.take 4 := by simp [hlen]
    _ = [A.val[0], A.val[1], A.val[2], A.val[3]] := htake

theorem sumRemaining_array4 (A : algo.U32X4) :
    sumRemaining ⟨Array.to_slice A, 0⟩ = sum4 (laneValues A) := by
  have hlist := congrArg (fun l : List U32 => (l.map UScalar.val).sum)
    (array4_list A)
  calc
    sumRemaining ⟨Array.to_slice A, 0⟩ =
        (A.val.map UScalar.val).sum := by simp [sumRemaining, Array.to_slice]
    _ = A.val[0].val + A.val[1].val + A.val[2].val + A.val[3].val := by
      simpa only [List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero, Nat.add_assoc] using hlist
    _ = sum4 (laneValues A) := rfl

theorem sum4_correctedValues (a b : Lanes) :
    sum4 (correctedValues a b) =
      4 * sum4 b + correction a := by
  simp only [sum4, correctedValues, correction]
  norm_num
  ring

/-- The exact generated suffix after lane reduction and scalar `b3` are known. -/
def finalCombine (a0 c : U32) (A B : algo.U32X4) : Result (U32 × U32) := do
  let C ← correctLanes A B
  let s ← lift (Array.to_slice A)
  let iter ← core.slice.Slice.iter s
  let a ← algo.Adler32.compute_loop2 iter a0
  let s1 ← lift (Array.to_slice C)
  let iter2 ← core.slice.Slice.iter s1
  let b ← algo.Adler32.compute_loop3 iter2 c
  .ok (a, b)

theorem finalCombine_generated (a0 c : U32) (A B : algo.U32X4) :
    (do
      let b_vec3 ← algo.U32X4.Insts.CoreOpsArithMulAssignU32.mul_assign B 4#u32
      let i8 ← Array.index_usize A 1#usize
      let i9 ← algo.Adler32.compute.MOD - i8
      let i10 ← Array.index_usize b_vec3 1#usize
      let i11 ← i10 + i9
      let a2 ← Array.update b_vec3 1#usize i11
      let i12 ← Array.index_usize A 2#usize
      let i13 ← algo.Adler32.compute.MOD - i12
      let i14 ← i13 * 2#u32
      let i15 ← Array.index_usize a2 2#usize
      let i16 ← i15 + i14
      let a3 ← Array.update a2 2#usize i16
      let i17 ← Array.index_usize A 3#usize
      let i18 ← algo.Adler32.compute.MOD - i17
      let i19 ← i18 * 3#u32
      let i20 ← Array.index_usize a3 3#usize
      let i21 ← i20 + i19
      let a4 ← Array.update a3 3#usize i21
      let s ← lift (Array.to_slice A)
      let iter1 ← core.slice.Slice.iter s
      let a5 ← algo.Adler32.compute_loop2 iter1 a0
      let s1 ← lift (Array.to_slice a4)
      let iter2 ← core.slice.Slice.iter s1
      let b4 ← algo.Adler32.compute_loop3 iter2 c
      .ok (a5, b4)) = finalCombine a0 c A B := by
  simp only [finalCombine, correctLanes, Aeneas.Std.bind_assoc]

theorem finalCombine_spec (a0 c : U32) (A B : algo.U32X4)
    (ha0 : a0.val ≤ 65535) (hc : c.val < modulus)
    (hA : ∀ i : Fin 4, laneValues A i < modulus)
    (hB : ∀ i : Fin 4, laneValues B i < modulus) :
    ∃ a b : U32, finalCombine a0 c A B = .ok (a, b) ∧
      a.val = a0.val + sum4 (laneValues A) ∧
      b.val = c.val + 4 * sum4 (laneValues B) + correction (laneValues A) ∧
      a.val ≤ 327615 ∧ b.val ≤ 1506966 := by
  have ha0' := hA 0
  have ha1 := hA 1
  have ha2 := hA 2
  have ha3 := hA 3
  have hb0 := hB 0
  have hb1 := hB 1
  have hb2 := hB 2
  have hb3 := hB 3
  have haBound : a0.val + sum4 (laneValues A) ≤ 327615 := by
    simp only [sum4, laneValues, modulus] at *
    omega
  have hbBound : c.val + 4 * sum4 (laneValues B) +
      correction (laneValues A) ≤ 1506966 := by
    simp only [sum4, correction, laneValues, modulus] at *
    omega
  obtain ⟨C, hC, hCval⟩ :=
    result_ok_of_spec _ _ (correctLanes_spec A B hA hB)
  have hsumC : c.val + sumRemaining ⟨Array.to_slice C, 0⟩ ≤ 1506966 := by
    rw [sumRemaining_array4, hCval, sum4_correctedValues]
    simpa only [Nat.add_assoc] using hbBound
  obtain ⟨a, ha, haven, habound⟩ :=
    compute_loop2_spec ⟨Array.to_slice A, 0⟩ a0 (by simp)
      (by rw [sumRemaining_array4]; omega)
  obtain ⟨b, hb, hbven, hbbound⟩ :=
    compute_loop3_spec ⟨Array.to_slice C, 0⟩ c (by simp) hsumC
  refine ⟨a, b, ?_, ?_, ?_, ?_, ?_⟩
  · unfold finalCombine
    simp [hC, lift, core.slice.Slice.iter, ha, hb]
  · rw [haven, sumRemaining_array4]
  · rw [hbven, sumRemaining_array4, hCval, sum4_correctedValues]
    omega
  · rw [haven, sumRemaining_array4]
    exact haBound
  · rw [hbven, sumRemaining_array4, hCval, sum4_correctedValues]
    simpa only [Nat.add_assoc] using hbBound

theorem finalCombine_laneInv (a0 c : U32) (A B : algo.U32X4)
    (ra rb : Nat)
    (ha0 : a0.val ≤ 65535) (hc : c.val < modulus)
    (hA : ∀ i : Fin 4, laneValues A i < modulus)
    (hB : ∀ i : Fin 4, laneValues B i < modulus)
    (hinv : laneInv a0.val c.val ra rb (laneValues A) (laneValues B))
    (hra : ra < modulus) (hrb : rb < modulus) :
    ∃ a b : U32, finalCombine a0 c A B = .ok (a, b) ∧
      a.val % modulus = ra ∧ b.val % modulus = rb ∧
      a.val ≤ 327615 ∧ b.val ≤ 1506966 := by
  obtain ⟨a, b, hresult, hav, hbv, habound, hbbound⟩ :=
    finalCombine_spec a0 c A B ha0 hc hA hB
  obtain ⟨hra', hrb'⟩ :=
    laneInv_combine a0.val c.val ra rb (laneValues A) (laneValues B)
      hinv hra hrb hA
  refine ⟨a, b, hresult, ?_, ?_, habound, hbbound⟩
  · rw [hav]
    exact hra'
  · rw [hbv]
    exact hrb'

end adler2
