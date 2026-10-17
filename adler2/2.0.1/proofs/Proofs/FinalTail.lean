module
public import Proofs.FinalCombine
public import Proofs.RawBridge

@[expose] public section

open Aeneas Aeneas.Std

namespace adler2

def finalTail (a5 b4 : U32) (tail : Slice U8) : Result Adler32 := do
  let iter3 ← core.slice.Slice.iter tail
  let (a6, b5) ← algo.Adler32.compute_loop4 iter3 a5 b4
  let i22 ← a6 % algo.Adler32.compute.MOD
  let i23 ← lift (UScalar.cast .U16 i22)
  let i24 ← b5 % algo.Adler32.compute.MOD
  let i25 ← lift (UScalar.cast .U16 i24)
  .ok { a := i23, b := i25 }

theorem finalTail_generated (a5 b4 : U32) (tail : Slice U8) :
    (do
      let iter3 ← core.slice.Slice.iter tail
      let (a6, b5) ← algo.Adler32.compute_loop4 iter3 a5 b4
      let i22 ← a6 % algo.Adler32.compute.MOD
      let i23 ← lift (UScalar.cast .U16 i22)
      let i24 ← b5 % algo.Adler32.compute.MOD
      let i25 ← lift (UScalar.cast .U16 i24)
      .ok { a := i23, b := i25 }) = finalTail a5 b4 tail := by
  rfl

theorem finalTail_spec (a5 b4 : U32) (tail : Slice U8)
    (ha5 : a5.val ≤ 327615) (hb4 : b4.val ≤ 1506966)
    (htail : tail.val.length ≤ 3) :
    ∃ out : Adler32,
      finalTail a5 b4 tail = .ok out ∧
      observe out = run (a5.val, b4.val) tail.val := by
  have hloA : a5.val + 255 * tail.val.length ≤ 328380 := by omega
  have hloB : b4.val + 328380 * tail.val.length ≤ 2492106 := by omega
  obtain ⟨⟨a6, b5⟩, hloop, hraw, ha6, hb5⟩ :=
    compute_loop4_spec ⟨tail, 0⟩ a5 b4 (by simp)
      (by simpa using hloA) (by simpa using hloB)
  have hraw' : (a6.val, b5.val) = rawRun (a5.val, b4.val) tail.val := by
    simpa using hraw
  have hmod : algo.Adler32.compute.MOD.val = modulus := by
    unfold algo.Adler32.compute.MOD modulus
    decide
  obtain ⟨i22, hi22, hi22val⟩ :=
    u32_rem_ok a6 algo.Adler32.compute.MOD (by simp [hmod, modulus])
  obtain ⟨i24, hi24, hi24val⟩ :=
    u32_rem_ok b5 algo.Adler32.compute.MOD (by simp [hmod, modulus])
  let i23 : U16 := UScalar.cast .U16 i22
  let i25 : U16 := UScalar.cast .U16 i24
  have hi23 : i23.val = a6.val % modulus := by
    simp only [i23, UScalar.cast_val_eq]
    change i22.val % 65536 = a6.val % modulus
    rw [hi22val, hmod]
    have hlt : a6.val % modulus < 65536 := by
      have := Nat.mod_lt a6.val modulus_pos
      simp only [modulus] at this ⊢
      omega
    exact Nat.mod_eq_of_lt hlt
  have hi25 : i25.val = b5.val % modulus := by
    simp only [i25, UScalar.cast_val_eq]
    change i24.val % 65536 = b5.val % modulus
    rw [hi24val, hmod]
    have hlt : b5.val % modulus < 65536 := by
      have := Nat.mod_lt b5.val modulus_pos
      simp only [modulus] at this ⊢
      omega
    exact Nat.mod_eq_of_lt hlt
  refine ⟨{ a := i23, b := i25 }, ?_, ?_⟩
  · simp [finalTail, core.slice.Slice.iter, hloop, hi22, hi24,
      lift, i23, i25]
  · change (i23.val, i25.val) = run (a5.val, b4.val) tail.val
    rw [hi23, hi25]
    have hnorm := normalize_rawRun (a5.val, b4.val) tail.val
    rw [← hraw'] at hnorm
    exact hnorm

end adler2
