import IntegerCore
import VarintSpec
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace integer_encoding

theorem total_result {α : Type _} {m : Result α} {p : α → Prop}
    (h : WP.spec m p) : ∃ value, m = Result.ok value ∧ p value := by
  cases m using Result.cases with
  | ret value => exact ⟨value,rfl,(WP.spec_ok value).mp h⟩
  | vis effect k => exact False.elim ((WP.spec_vis effect k).mp h)
  | div => exact False.elim (WP.spec_div.mp h)

theorem zigzag_encode_bits (x : I64) :
    ∃ out, varint.zigzag_encode x = .ok out ∧
      out.bv = (x.bv <<< 1) ^^^ x.bv.sshiftRight 63 := by
  apply total_result
  unfold varint.zigzag_encode
  step
  step
  step
  have hc := IScalar.hcast_bv_eq .U64 i2
  have hs : i2.bv.signExtend UScalarTy.U64.numBits = i2.bv := BitVec.signExtend_eq _
  exact hc.trans (hs.trans (i2_post1.trans (congrArg₂ (fun a b : BitVec 64 => a ^^^ b) i_post1 i1_post1)))
theorem sign_mask (x : BitVec 64) :
    x.sshiftRight 63 = if x.msb then BitVec.allOnes 64 else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight]
  have hle : ¬64 ≤ i := by omega
  simp only [hle, decide_false, Bool.not_false, Bool.true_and]
  by_cases hz : i = 0
  · subst i
    simp only [Nat.add_zero, show 63 < 64 by decide, ↓reduceIte]
    have hm : x.getLsbD 63 = x.msb := rfl
    rw [hm]
    cases h : x.msb
    · change false = (0 : BitVec 64).getLsbD 0
      rfl
    · change true = (BitVec.allOnes 64).getLsbD 0
      exact (BitVec.getLsbD_allOnes (v := 64) (i := 0)).symm
  · have hbound : ¬63+i <64 := by omega
    simp only [hbound, ↓reduceIte]
    cases h : x.msb
    · change false = (0 : BitVec 64).getLsbD i
      exact BitVec.getLsbD_zero.symm
    · change true = (BitVec.allOnes 64).getLsbD i
      exact ((BitVec.getLsbD_allOnes (v := 64) (i := i)).trans (by simp only [hi,decide_true])).symm

theorem encode_bv_form (x : BitVec 64) :
    (x <<< 1) ^^^ x.sshiftRight 63 = if x.msb then ~~~(x <<< 1) else x <<< 1 := by
  rw [sign_mask]
  cases h : x.msb
  · exact BitVec.xor_zero
  · exact BitVec.xor_allOnes
theorem encode_arithmetic (x : I64) :
    ((x.bv <<< 1) ^^^ x.bv.sshiftRight 63).toNat = IntegerEncodingSpec.zigzag x.val := by
  have hb := x.bv.isLt
  have hx : x.val = if x.bv.msb then (x.bv.toNat : Int) - (2: Int)^64 else (x.bv.toNat : Int) :=
    BitVec.toInt_eq_msb_cond x.bv
  rw [encode_bv_form]
  cases hm : x.bv.msb
  · have hn := BitVec.toNat_lt_of_msb_false hm
    simp only [hm, Bool.false_eq_true, ↓reduceIte] at hx ⊢
    have hz : 0 ≤ x.val := by omega
    simp only [IntegerEncodingSpec.zigzag, hz, ↓reduceIte, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    norm_num at hb hn hx ⊢
    omega
  · have hn := BitVec.toNat_ge_of_msb_true hm
    simp only [hm, ↓reduceIte] at hx ⊢
    have hz : ¬0 ≤ x.val := by norm_num at hx hb; omega
    simp only [IntegerEncodingSpec.zigzag, hz, ↓reduceIte, BitVec.toNat_not,
      BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    norm_num at hb hn hx ⊢
    omega

theorem zigzag_encode_spec (x : I64) :
    ∃ out, varint.zigzag_encode x = .ok out ∧ out.val = IntegerEncodingSpec.zigzag x.val := by
  obtain ⟨out,ho,hv⟩ := zigzag_encode_bits x
  exact ⟨out,ho,(congrArg BitVec.toNat hv).trans (encode_arithmetic x)⟩
end integer_encoding
