import Mathlib.Data.Nat.Log
namespace IntegerEncodingSpec

/-- Length of the unique minimal positive base-128 digit representation, including zero. -/
def uLen (n : Nat) : Nat := Nat.log 128 n + 1

theorem uLen_pos (n : Nat) : 1 ≤ uLen n := by unfold uLen; omega

theorem uLen_small {n : Nat} (h : n < 128) : uLen n = 1 := by
  simp [uLen, Nat.log_of_lt h]

theorem uLen_step {n : Nat} (h : 128 ≤ n) : uLen n = uLen (n / 128) + 1 := by
  unfold uLen
  rw [Nat.log_of_one_lt_of_le (by decide : 1 < 128) h]

theorem uLen_bound (n : Nat) : n < 128 ^ uLen n :=
  Nat.lt_pow_succ_log_self (by decide) n

theorem uLen_minimal (n k : Nat) (hk : 1 ≤ k) (h : n < 128^k) : uLen n ≤ k := by
  unfold uLen
  have hl := Nat.log_lt_of_lt_pow' (by omega : k ≠ 0) h
  omega

theorem uLen_le10 {n : Nat} (h : n < 2^64) : uLen n ≤ 10 := by
  apply uLen_minimal n 10 (by decide)
  have hp : 2^64 ≤ (128 : Nat)^10 := by decide
  omega

/-- Signed ZigZag arithmetic, independent of fixed-width bitwise implementation. -/
def zigzag (z : Int) : Nat := if 0 ≤ z then (2*z).toNat else (-2*z-1).toNat
end IntegerEncodingSpec
