import Zigzag
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace integer_encoding
def zigzagDecode (n : Nat) : Int :=
  if n % 2 = 0 then (n/2 : Int) else -(n/2 : Int)-1

theorem hcast_lowbit (x : U64) (hx : x.val ≤ 1) :
    (UScalar.hcast .I64 x).val = (x.val : Int) := by
  have hc : x.val = 0 ∨ x.val = 1 := by omega
  rcases hc with h|h <;> simp only [UScalar.hcast_val_eq,h] <;> norm_num

theorem zigzag_decode_spec (x : U64) :
    ∃ out, varint.zigzag_decode x = .ok out ∧ out.val = zigzagDecode x.val := by
  apply total_result
  unfold varint.zigzag_decode
  step
  step
  step
  have hb : i1.val ≤ 1 := by
    simpa [i1_post, UScalar.val_and] using (Nat.and_le_right : x.val &&& 1 ≤ 1)
  have hi2 : i2.val = (i1.val : Int) := by rw [i2_post]; exact hcast_lowbit i1 hb
  step
  step
  step
  have hbit : i1.val = x.val % 2 := by simpa [UScalar.val_and] using i1_post
  have hhalf : i.val = x.val / 2 := by simpa [Nat.shiftRight_eq_div_pow] using i_post
  have hxbound := x.hmax
  have hc : (UScalar.hcast .I64 i5).val = (i5.val : Int).bmod (2^64) :=
    UScalar.hcast_val_eq _ _
  rw [hc]
  by_cases hz : x.val % 2 = 0
  · have h3 : i3.val = 0 := by omega
    have h4 : i4.val = 0 := by
      rw [i4_post]
      simp only [IScalar.hcast_val_eq,h3]
      norm_num
    have he4 : i4.bv = (0 : BitVec 64) := by apply BitVec.eq_of_toNat_eq; exact h4
    have hb5 : i5.bv = i.bv := i5_post1.trans
      ((congrArg (fun a : BitVec 64 => i.bv ^^^ a) he4).trans BitVec.xor_zero)
    have h5 : i5.val = i.val := congrArg BitVec.toNat hb5
    simp only [zigzagDecode,hz,↓reduceIte]
    rw [h5, Int.bmod_eq_emod]
    norm_num [UScalarTy.numBits] at hxbound ⊢
    omega
  · have hmod : x.val % 2 = 1 := by omega
    have h3 : i3.val = -1 := by omega
    have h4 : i4.val = 18446744073709551615 := by
      rw [i4_post]
      simp only [IScalar.hcast_val_eq,h3]
      norm_num
    have hb4 : i4.bv = BitVec.allOnes 64 := by
      apply BitVec.eq_of_toNat_eq
      exact h4
    have hb5 : i5.bv = ~~~i.bv :=
      i5_post1.trans ((congrArg (fun a : BitVec 64 => i.bv ^^^ a) hb4).trans BitVec.xor_allOnes)
    have h5 : i5.val = 2^64-1-i.val := (congrArg BitVec.toNat hb5).trans BitVec.toNat_not
    simp only [zigzagDecode,hz,↓reduceIte]
    rw [h5, Int.bmod_eq_emod]
    norm_num [UScalarTy.numBits] at hxbound ⊢
    omega
end integer_encoding
