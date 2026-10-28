module
public import Proofs.IPv4SubnetMath

public section

namespace IPv4SubnetStateMath

open RangeMath

def residualBlock (s e b : Nat) : HalfOpen :=
  if s + b < e + 1 then .live (s + b) (e + 1) else .empty

theorem residualBlock_eq_selected (s e q b : Nat)
    (hq : q ≤ 32) (hse : s ≤ e)
    (hb : b = IPv4SubnetMath.blockSize s (e+1) q hq (by omega)) :
    residualBlock s e b = IPv4SubnetMath.residual s (e+1) q hq (by omega) := by
  simp [residualBlock, IPv4SubnetMath.residual, hb]

theorem saturated_iff_max (s e b u v : Nat)
    (_hse : s ≤ e) (he : e < limit)
    (_hb : 0 < b) (hfit : s + b ≤ e + 1)
    (hu : u + 1 = s + b)
    (hv : v = min (u + 1) maxAddress) :
    v = u ↔ u = maxAddress := by
  have hemax : e ≤ maxAddress := by
    rw [maxAddress_eq]
    norm_num [limit] at he
    omega
  have huBound : u ≤ maxAddress := by omega
  rw [maxAddress_eq] at *
  simp only [min_def] at hv
  split at hv <;> omega

theorem saturated_residual_empty (s e b u v : Nat)
    (hse : s ≤ e) (he : e < limit)
    (hb : 0 < b) (hfit : s + b ≤ e + 1)
    (hu : u + 1 = s + b)
    (hv : v = min (u + 1) maxAddress)
    (hsat : v = u) :
    residualBlock s e b = .empty ∧ ofInclusive v 0 = .empty := by
  have humax := (saturated_iff_max s e b u v hse he hb hfit hu hv).1 hsat
  have hemax : e = maxAddress := by
    have he' : e ≤ maxAddress := by
      rw [maxAddress_eq]
      norm_num [limit] at he
      omega
    omega
  have hterminal : s + b = e + 1 := by omega
  constructor
  · simp [residualBlock, hterminal]
  · have hvpos : 0 < v := by rw [hsat, humax, maxAddress_eq]; norm_num
    simp [ofInclusive, Nat.not_le.mpr hvpos]

theorem unsaturated_residual (s e b u v : Nat)
    (hse : s ≤ e) (he : e < limit)
    (hb : 0 < b) (hfit : s + b ≤ e + 1)
    (hu : u + 1 = s + b)
    (hv : v = min (u + 1) maxAddress)
    (hunsat : v ≠ u) :
    ofInclusive v e = residualBlock s e b := by
  have hneq : u ≠ maxAddress := by
    intro h
    exact hunsat ((saturated_iff_max s e b u v hse he hb hfit hu hv).2 h)
  have huBound : u ≤ maxAddress := by
    have hemax : e ≤ maxAddress := by
      rw [maxAddress_eq]
      norm_num [limit] at he
      omega
    omega
  have hvEq : v = s + b := by
    have : u + 1 ≤ maxAddress := by omega
    calc
      v = u + 1 := by rw [hv, Nat.min_eq_left this]
      _ = s + b := hu
  by_cases hmore : s + b < e + 1
  · have hle : s + b ≤ e := by omega
    simp [ofInclusive, residualBlock, hvEq, hmore, hle]
  · have heq : s + b = e + 1 := by omega
    have hnot : ¬ s + b ≤ e := by omega
    simp [ofInclusive, residualBlock, hvEq, hmore, hnot]

theorem singleton_residual_empty (s b u v : Nat)
    (_hs : s < limit) (hb : 0 < b) (hfit : s + b ≤ s + 1)
    (hu : u + 1 = s + b)
    (hv : v = min (u + 1) maxAddress) :
    residualBlock s s b = .empty ∧ ofInclusive v 0 = .empty := by
  have hb1 : b = 1 := by omega
  have huEq : u = s := by omega
  have hvpos : 0 < v := by
    have hm : 0 < maxAddress := by rw [maxAddress_eq]; norm_num
    simp [hv, huEq]
    omega
  constructor
  · simp [residualBlock, hb1]
  · simp [ofInclusive, Nat.not_le.mpr hvpos]

end IPv4SubnetStateMath
