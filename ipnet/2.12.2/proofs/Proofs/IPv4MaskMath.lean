module
public import Ipnet

public section

namespace IPv4MaskMath
open Aeneas Aeneas.Std Result
theorem mask_core (C D v z : Nat) (hC : 0 < C) (hD : 0 < D)
    (hz : z < D) (hvz : v + z + 1 = C * D) :
    (v * C) % (D * C) = 0 ↔ v = C * D - D := by
  rw [Nat.mul_mod_mul_right]
  constructor
  · intro h
    have hmod : v % D = 0 := by
      rcases Nat.mul_eq_zero.mp h with h0 | h0
      · exact h0
      · omega
    have hdiv : v = D * (v / D) := by
      have := Nat.mod_add_div v D
      omega
    have hq : v / D + 1 = C := by nlinarith
    have hc1 : C * D - D = (C - 1) * D := by
      rw [Nat.sub_mul]
      simp
    rw [hc1]
    have : C - 1 = v / D := by omega
    rw [this]
    simpa [Nat.mul_comm] using hdiv
  · intro hv
    have hc1 : C * D - D = (C - 1) * D := by
      rw [Nat.sub_mul]
      simp
    rw [hv, hc1]
    simp
theorem lz_val (v : U32) : (core.num.U32.leading_zeros (~~~v)).val =
    (if (~~~v).val = 0 then 32 else 32 - Nat.log 2 (~~~v).val - 1) := by
  simp only [core.num.U32.leading_zeros, BitVec.leadingZeros]
  change (BitVec.ofNat 32 (if ~~~v.bv = 0 then 32 else
      32 - Nat.log 2 (~~~v).bv.toNat - 1)).toNat =
      if (~~~v.bv).toNat = 0 then 32 else 32 - Nat.log 2 (~~~v).bv.toNat - 1
  rw [BitVec.toNat_ofNat]
  by_cases hz : ~~~v.bv = 0
  · have hzv : (~~~v.bv).toNat = 0 := by simp [hz]
    simp [hz]
  · have hzv : (~~~v.bv).toNat ≠ 0 := by
      intro he
      apply hz
      apply BitVec.eq_of_toNat_eq
      simpa using he
    simp only [hz, hzv, ↓reduceIte]
    apply Nat.mod_eq_of_lt
    omega
theorem not_val (v : U32) : (~~~v).val = 2^32 - 1 - v.val := by
  change (~~~v.bv).toNat = 2 ^ 32 - 1 - v.bv.toNat
  exact BitVec.toNat_not
theorem mask_numeric_iff (v : U32) :
    let p := (core.num.U32.leading_zeros (~~~v)).val
    (v.val * 2 ^ p) % 2 ^ 32 = 0 ↔ v.val = 2 ^ 32 - 2 ^ (32-p) := by
  dsimp
  let z := (~~~v).val
  let p := (core.num.U32.leading_zeros (~~~v)).val
  change (v.val * 2 ^ p) % 2 ^ 32 = 0 ↔ v.val = 2 ^ 32 - 2 ^ (32-p)
  have hnot : z = 2 ^ 32 - 1 - v.val := not_val v
  have hvbound : v.val < 2 ^ 32 := by exact v.bv.isLt
  have hzbound : z < 2 ^ 32 := by exact (~~~v).bv.isLt
  have hvz : v.val + z + 1 = 2 ^ 32 := by omega
  by_cases hz : z = 0
  · have hp : p = 32 := by simp [p, lz_val, z, hz]
    have hv : v.val = 2 ^ 32 - 1 := by omega
    simp [hp, hv]
  · have hk : Nat.log 2 z < 32 :=
      (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) hz).2 hzbound
    have hp : p = 31 - Nat.log 2 z := by
      dsimp [p]
      rw [lz_val]
      change (if z = 0 then 32 else 32 - Nat.log 2 z - 1) =
        31 - Nat.log 2 z
      simp only [hz, ↓reduceIte]
      omega
    have hps : p + (Nat.log 2 z + 1) = 32 := by omega
    have hs : 32 - p = Nat.log 2 z + 1 := by omega
    have hzD : z < 2 ^ (32-p) := by
      rw [hs]
      exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) z
    have hpow : 2 ^ 32 = 2 ^ p * 2 ^ (32-p) := by
      rw [← pow_add]
      congr 1
      omega
    have hcore := mask_core (2^p) (2^(32-p)) v.val z
      (by positivity) (by positivity) hzD (by rw [←hpow]; exact hvz)
    simpa only [hpow, Nat.mul_comm] using hcore

theorem log_pow_sub_one (k : Nat) (hk : 0 < k) :
    Nat.log 2 (2 ^ k - 1) = k - 1 := by
  have hpow : 2 ^ k = 2 ^ (k-1) * 2 := by
    conv_lhs => rw [show k = k - 1 + 1 by omega, pow_succ]
  have hbase : 0 < 2 ^ (k-1) := by positivity
  have hleft : 2 ^ (k-1) ≤ 2 ^ k - 1 := by
    rw [hpow]
    omega
  have hright : 2 ^ k - 1 < 2 ^ ((k-1)+1) := by
    have he : (k-1)+1 = k := by omega
    rw [he]
    omega
  apply (Nat.log_eq_iff (Or.inr ⟨by decide, ?_⟩)).2
  · exact ⟨hleft, hright⟩
  · rw [hpow]
    omega
theorem valid_mask_prefix (v : U32) (q : Nat) (hq : q ≤ 32)
    (hv : v.val = 2 ^ 32 - 2 ^ (32-q)) :
    (core.num.U32.leading_zeros (~~~v)).val = q := by
  have hz := IPv4MaskMath.not_val v
  have hD : 2 ^ (32-q) ≤ 2 ^ 32 := by gcongr; omega
  have hvbound : v.val < 2 ^ 32 := v.bv.isLt
  have hzval : (~~~v).val = 2 ^ (32-q) - 1 := by omega
  rw [IPv4MaskMath.lz_val, hzval]
  by_cases hq32 : q = 32
  · subst q
    simp
  · have hk : 0 < 32-q := by omega
    have hzpos : 2 ^ (32-q) - 1 ≠ 0 := by
      have : 2 ≤ 2 ^ (32-q) := by
        have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ 32-q by omega)
        norm_num at hpow
        exact hpow
      omega
    simp only [hzpos, ↓reduceIte]
    rw [log_pow_sub_one (32-q) hk]
    omega

end IPv4MaskMath
