module
public import Proofs.CidrModel

public section

namespace NetworkMath

/-- Clearing the low `s` bits gives the arithmetic block base, for every
width-bounded address. -/
theorem and_high_mask (w a s : Nat) (hs : s ≤ w) (ha : a < 2 ^ w) :
    a &&& (2 ^ w - 2 ^ s) = (a / 2 ^ s) * 2 ^ s := by
  have hpow : 2 ^ w = 2 ^ (w - s) * 2 ^ s := by
    have he : (w - s) + s = w := by omega
    rw [← pow_add, he]
  have hfactor : 2 ^ w - 2 ^ s = (2 ^ (w - s) - 1) * 2 ^ s := by
    rw [hpow, Nat.sub_mul]
    simp
  apply Nat.eq_of_testBit_eq
  intro i
  rw [hfactor, Nat.testBit_and, Nat.testBit_mul_two_pow,
    Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases his : s ≤ i
  · simp only [decide_eq_true his, Bool.true_and]
    by_cases hiw : i < w
    · have hsub : i - s < w - s := by omega
      simp [hsub, Nat.sub_add_cancel his]
    · have hge : w ≤ i := by omega
      have hz : a.testBit i = false := by
        have hpowle : 2 ^ w ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hge
        exact Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hpowle)
      simp [show ¬ i - s < w - s by omega, Nat.sub_add_cancel his, hz]
  · have hlt : i < s := by omega
    simp [his]

/-- Setting every low bit gives the arithmetic end of the address block. -/
theorem or_low_mask (a s : Nat) :
    a ||| (2 ^ s - 1) = (a / 2 ^ s) * 2 ^ s + 2 ^ s - 1 := by
  have hp : 0 < 2 ^ s := by positivity
  have hlt : 2 ^ s - 1 < 2 ^ s := by omega
  have hadd : (a / 2 ^ s) * 2 ^ s + 2 ^ s - 1 =
      (a / 2 ^ s) * 2 ^ s + (2 ^ s - 1) := by omega
  rw [hadd, Nat.mul_comm (a / 2 ^ s) (2 ^ s),
    Nat.two_pow_add_eq_or_of_lt hlt]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow_mul, Nat.testBit_div_two_pow]
  by_cases hi : i < s
  · simp [hi]
  · have hs : s ≤ i := by omega
    simp [hi, hs, Nat.sub_add_cancel hs]

theorem and_netmask_eq_lower (w a p : Nat)
    (_hp : p ≤ w) (ha : a < 2 ^ w) :
    a &&& (2 ^ w - 2 ^ (w - p)) = CidrModel.lower w a p := by
  exact and_high_mask w a (w - p) (Nat.sub_le w p) ha

theorem or_hostmask_eq_upper (w a p : Nat) :
    a ||| (2 ^ (w - p) - 1) = CidrModel.upper w a p := by
  simpa only [CidrModel.upper, CidrModel.lower, CidrModel.size] using
    or_low_mask a (w - p)

end NetworkMath
