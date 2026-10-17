module
public import Proofs.IPv6SubnetMath

public section
open Aeneas Aeneas.Std
namespace IPv6SubnetBits
theorem lz_eq_clz (x : BitVec 128) :
    Aeneas.Std.BitVec.leadingZeros x = x.clz.toNat := by
  by_cases hx : x = 0#128
  · have hc : x.clz.toNat = 128 := by
      have hh := (BitVec.clz_eq_iff_eq_zero (x := x)).2 hx
      rw [hh]
      decide
    simp [Aeneas.Std.BitVec.leadingZeros, hx]
  · have hc : x.clz.toNat < 128 := by
      have hh := (BitVec.clz_lt_iff_ne_zero (x := x)).2 hx
      simpa [BitVec.lt_def] using hh
    have hlo := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (by omega : 0 < 128) hx
    have hhi := BitVec.toNat_lt_two_pow_sub_clz (x := x)
    have hlog : Nat.log 2 x.toNat = 127 - x.clz.toNat := by
      apply (Nat.log_eq_iff (Or.inr ⟨by decide, ?_⟩)).2
      · constructor
        · simpa [show 128 - 1 - x.clz.toNat = 127 - x.clz.toNat by omega] using hlo
        · simpa [show 127 - x.clz.toNat + 1 = 128 - x.clz.toNat by omega] using hhi
      · intro hz
        exact hx (BitVec.eq_of_toNat_eq (by simpa using hz))
    simp [Aeneas.Std.BitVec.leadingZeros, hx, hlog]
    omega
theorem mod_pow_iff_bits (n k : Nat) :
    n % 2 ^ k = 0 ↔ ∀ i < k, n.testBit i = false := by
  constructor
  · intro h i hi
    have hb := congrArg (fun x : Nat => x.testBit i) h
    simpa [Nat.testBit_mod_two_pow, hi] using hb
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow]
    by_cases hi : i < k
    · simp [hi, h i hi]
    · simp [hi]

theorem ctz_mod_iff (x : BitVec 128) (j : Nat) (hj : j ≤ 128) :
    j ≤ x.ctz.toNat ↔ x.toNat % 2 ^ j = 0 := by
  constructor
  · intro h
    apply (mod_pow_iff_bits x.toNat j).2
    intro i hi
    have hb := BitVec.getLsbD_false_of_lt_ctz (x := x) (i := i) (by omega)
    exact hb
  · intro h
    by_contra hn
    have hlt : x.ctz.toNat < j := by omega
    have hx : x ≠ 0#128 := by
      apply (BitVec.ctz_lt_iff_ne_zero (x := x)).1
      simpa [BitVec.lt_def] using (show x.ctz.toNat < 128 by omega)
    have hb := BitVec.getLsbD_true_ctz_of_ne_zero (x := x) hx
    have hf := (mod_pow_iff_bits x.toNat j).1 h x.ctz.toNat hlt
    simp [BitVec.getLsbD] at hb
    simp_all

theorem trailing_zeros_value (x : U128) :
    ∃ out, core.num.U128.trailing_zeros x = Result.ok out ∧
      out.val = x.bv.ctz.toNat := by
  let out : U32 := ⟨BitVec.ofNat 32 (Aeneas.Std.BitVec.leadingZeros x.bv.reverse)⟩
  refine ⟨out, rfl, ?_⟩
  change (BitVec.ofNat 32 (Aeneas.Std.BitVec.leadingZeros x.bv.reverse)).toNat =
    x.bv.ctz.toNat
  rw [lz_eq_clz, ← BitVec.ctz_eq_reverse_clz]
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hc := BitVec.clz_le (x := x.bv.reverse)
  have hc' : x.bv.reverse.clz.toNat ≤ 128 := by
    simpa [BitVec.le_def] using hc
  rw [← BitVec.ctz_eq_reverse_clz] at hc'
  omega

theorem trailing_zeros_mod_spec (x : U128) (j : Nat) (hj : j ≤ 128) :
    ∃ out, core.num.U128.trailing_zeros x = Result.ok out ∧
      (j ≤ out.val ↔ x.val % 2 ^ j = 0) := by
  rcases trailing_zeros_value x with ⟨out, hout, hval⟩
  refine ⟨out, hout, ?_⟩
  rw [hval]
  exact ctz_mod_iff x.bv j hj

theorem trailing_zeros_le_width (x : U128) :
    ∃ z, core.num.U128.trailing_zeros x = Result.ok z ∧ z.val ≤ 128 := by
  rcases trailing_zeros_value x with ⟨z, hz, hval⟩
  refine ⟨z, hz, ?_⟩
  rw [hval, BitVec.ctz_eq_reverse_clz]
  have hc := BitVec.clz_le (x := x.bv.reverse)
  simpa [BitVec.le_def] using hc

theorem start_prefix_alignment (x : U128) (p : Nat) (hp : p ≤ 128) :
    ∃ z, core.num.U128.trailing_zeros x = Result.ok z ∧
      (128 - z.val ≤ p ↔ x.val % 2 ^ (128-p) = 0) := by
  rcases trailing_zeros_value x with ⟨z, hz, hval⟩
  refine ⟨z, hz, ?_⟩
  have htz : z.val ≤ 128 := by
    rw [hval, BitVec.ctz_eq_reverse_clz]
    have hc := BitVec.clz_le (x := x.bv.reverse)
    simpa [BitVec.le_def] using hc
  have hmod := ctz_mod_iff x.bv (128-p) (by omega)
  rw [← hval] at hmod
  constructor
  · intro h
    apply hmod.mp
    omega
  · intro h
    have hj := hmod.mpr h
    omega
end IPv6SubnetBits
