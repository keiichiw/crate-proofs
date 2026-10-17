module
public import Adler2

public section

open Aeneas.Std

namespace adler2

theorem checksum_spec (s : Adler32) :
    ∃ out : U32, Adler32.checksum s = Result.ok out ∧
      out.val = s.b.val * 65536 + s.a.val := by
  have hshift : (core.convert.num.FromU32U16.from s.b <<< 16#i32) =
      Result.ok (⟨(core.convert.num.FromU32U16.from s.b).bv <<< 16⟩ : U32) := by
    rfl
  simp only [Adler32.checksum, lift, bind_ok, hshift]
  refine ⟨_, rfl, ?_⟩
  change ((s.b.bv.setWidth 32 <<< 16 ||| s.a.bv.setWidth 32).toNat) =
    s.b.val * 65536 + s.a.val
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft]
  rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_setWidth_of_le (by decide)]
  have ha : s.a.val < 65536 := U16.lt_succ_max s.a
  have hb : s.b.val < 65536 := U16.lt_succ_max s.b
  have hprod : s.b.val <<< 16 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    omega
  change s.b.val <<< 16 % 2 ^ 32 ||| s.a.val = s.b.val * 65536 + s.a.val
  rw [Nat.mod_eq_of_lt hprod]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 16) (by omega : s.a.val < 2 ^ 16) s.b.val]
  rw [Nat.shiftLeft_eq]

theorem from_checksum_spec (sum : U32) :
    ∃ out : Adler32, Adler32.from_checksum sum = Result.ok out ∧
      out.a.val = sum.val % 65536 ∧ out.b.val = sum.val / 65536 := by
  have hshift : (sum >>> 16#i32) = Result.ok (⟨sum.bv >>> 16⟩ : U32) := by
    rfl
  simp only [Adler32.from_checksum, lift, bind_ok, hshift]
  refine ⟨_, rfl, ?_, ?_⟩
  · simp [UScalar.cast_val_eq]
  · change (UScalar.cast .U16 (⟨sum.bv >>> 16⟩ : U32)).val = sum.val / 65536
    rw [UScalar.cast_val_eq]
    change (sum.bv >>> 16).toNat % 65536 = sum.val / 65536
    rw [BitVec.toNat_ushiftRight]
    change sum.val >>> 16 % 65536 = sum.val / 65536
    rw [Nat.shiftRight_eq_div_pow]
    have hs : sum.val < 4294967296 := U32.lt_succ_max sum
    omega

theorem checksum_from_checksum (sum : U32) :
    (do
      let s ← Adler32.from_checksum sum
      Adler32.checksum s) = Result.ok sum := by
  obtain ⟨s, hs, ha, hb⟩ := from_checksum_spec sum
  obtain ⟨out, hout, hval⟩ := checksum_spec s
  rw [hs]
  simp only [bind_ok, hout]
  congr 1
  apply UScalar.eq_imp
  omega

theorem from_checksum_checksum (s : Adler32) :
    (do
      let c ← Adler32.checksum s
      Adler32.from_checksum c) = Result.ok s := by
  obtain ⟨c, hc, hval⟩ := checksum_spec s
  obtain ⟨out, hout, ha, hb⟩ := from_checksum_spec c
  rw [hc]
  simp only [bind_ok, hout]
  congr 1
  cases s with
  | mk a b =>
    cases out with
    | mk a' b' =>
      have haBound : a.val < 65536 := U16.lt_succ_max a
      have hbBound : b.val < 65536 := U16.lt_succ_max b
      simp only [Adler32.mk.injEq] at *
      have haEq : a'.val = a.val := by omega
      have hbEq : b'.val = b.val := by omega
      exact ⟨UScalar.eq_imp _ _ haEq, UScalar.eq_imp _ _ hbEq⟩

end adler2
