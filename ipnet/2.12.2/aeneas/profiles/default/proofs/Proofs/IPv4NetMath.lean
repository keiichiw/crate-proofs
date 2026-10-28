module
public import Proofs.RangeMath

public section

/-! Independent Nat arithmetic for the IPv4 network APIs. -/
namespace IPv4NetMath

@[expose] def hostStart (a p : Nat) : Nat :=
  if p < 31 then CidrModel.lower 32 a p + 1 else CidrModel.lower 32 a p

@[expose] def hostStop (a p : Nat) : Nat :=
  if p < 31 then CidrModel.upper 32 a p - 1 else CidrModel.upper 32 a p

@[expose] def hostsRemaining (a p : Nat) : RangeMath.HalfOpen :=
  RangeMath.ofInclusive (hostStart a p) (hostStop a p)

theorem size_ge_four (p : Nat) (hp : p < 31) :
    4 ≤ CidrModel.size 32 p := by
  have hexp : 2 ≤ 32 - p := by omega
  have hpow : 2 ^ 2 ≤ 2 ^ (32 - p) :=
    Nat.pow_le_pow_right (by omega) hexp
  simpa [CidrModel.size] using hpow

theorem host_adjustment_bounds (a p : Nat) (hp : p < 31) :
    CidrModel.lower 32 a p + 1 ≤ CidrModel.upper 32 a p - 1 ∧
      0 < CidrModel.upper 32 a p ∧
      CidrModel.upper 32 a p - 1 + 1 = CidrModel.upper 32 a p := by
  have hsize := size_ge_four p hp
  rw [CidrModel.upper_eq]
  omega

theorem host_start_no_saturation (a p : Nat)
    (hp : p < 31) (ha : a < RangeMath.limit) :
    min (CidrModel.lower 32 a p + 1) RangeMath.maxAddress =
      CidrModel.lower 32 a p + 1 := by
  have hle := (host_adjustment_bounds a p hp).1
  have hupper := CidrModel.upper_lt_width 32 a p (by omega)
    (by simpa [RangeMath.limit] using ha)
  have hmax : CidrModel.lower 32 a p + 1 ≤ RangeMath.maxAddress := by
    rw [RangeMath.maxAddress_eq]
    norm_num [RangeMath.limit] at hupper
    omega
  exact Nat.min_eq_left hmax

theorem host_endpoints_in_width (a p : Nat)
    (hp : p ≤ 32) (ha : a < RangeMath.limit) :
    hostStart a p < RangeMath.limit ∧ hostStop a p < RangeMath.limit := by
  have hupper := CidrModel.upper_lt_width 32 a p hp
    (by simpa [RangeMath.limit] using ha)
  have hupper' : CidrModel.upper 32 a p < RangeMath.limit := by
    simpa [RangeMath.limit] using hupper
  by_cases h : p < 31
  · obtain ⟨hle, _, _⟩ := host_adjustment_bounds a p h
    simp only [hostStart, hostStop, h, ↓reduceIte]
    omega
  · simp only [hostStart, hostStop, h, ↓reduceIte]
    have hlower := CidrModel.lower_le_upper 32 a p
    omega

theorem hosts_remaining_lt31 (a p : Nat) (hp : p < 31) :
    hostsRemaining a p =
      .live (CidrModel.lower 32 a p + 1) (CidrModel.upper 32 a p) := by
  obtain ⟨hle, _, hstop⟩ := host_adjustment_bounds a p hp
  simp only [hostsRemaining, hostStart, hostStop, hp, ↓reduceIte]
  rw [show RangeMath.ofInclusive (CidrModel.lower 32 a p + 1)
      (CidrModel.upper 32 a p - 1) =
      .live (CidrModel.lower 32 a p + 1)
        ((CidrModel.upper 32 a p - 1) + 1) by
        simp [RangeMath.ofInclusive, hle]]
  rw [hstop]

theorem hosts_remaining_ge31 (a p : Nat) (hp : 31 ≤ p) :
    hostsRemaining a p =
      .live (CidrModel.lower 32 a p) (CidrModel.upper 32 a p + 1) := by
  have hnot : ¬ p < 31 := by omega
  have hle := CidrModel.lower_le_upper 32 a p
  simp [hostsRemaining, hostStart, hostStop, hnot, RangeMath.ofInclusive, hle]

theorem hosts_remaining_nonempty (a p : Nat) (hp : p ≤ 32) :
    hostsRemaining a p ≠ .empty := by
  by_cases h : p < 31
  · rw [hosts_remaining_lt31 a p h]
    simp
  · have hge : 31 ≤ p := by omega
    rw [hosts_remaining_ge31 a p hge]
    simp

/-- A valid /p block lies in its immediate /p-1 parent, even when the stored
    address has host bits. -/
theorem parent_contains_child (a p : Nat) (hpos : 0 < p) (hp : p ≤ 32) :
    CidrModel.subset 32 a (p - 1) a p := by
  let k := CidrModel.size 32 p
  have hk : 0 < k := CidrModel.size_pos 32 p
  have hparent_size : CidrModel.size 32 (p - 1) = k * 2 := by
    have he : 32 - (p - 1) = (32 - p) + 1 := by omega
    simp [CidrModel.size, k, he, pow_succ]
  have hparent_lo : CidrModel.lower 32 a (p - 1) =
      (a / k / 2) * (k * 2) := by
    simp only [CidrModel.lower, hparent_size]
    rw [← Nat.div_div_eq_div_mul]
  have hchild_lo : CidrModel.lower 32 a p = (a / k) * k := rfl
  have hrem : (a / k) % 2 < 2 := Nat.mod_lt _ (by omega)
  have hdecomp : (a / k) % 2 + (a / k / 2) * 2 = a / k := by
    simpa [Nat.mul_comm] using Nat.mod_add_div (a / k) 2
  have hdelta : (a / k) * k =
      (a / k / 2) * (k * 2) + ((a / k) % 2) * k := by
    conv_lhs => rw [← hdecomp]
    ring
  have hdelta_le : ((a / k) % 2) * k ≤ k := by
    have hr : (a / k) % 2 ≤ 1 := by omega
    exact (Nat.mul_le_mul_right k hr).trans (by simp)
  rw [CidrModel.subset_iff_endpoints]
  rw [hparent_lo, hchild_lo]
  constructor
  · omega
  · rw [CidrModel.upper_eq, CidrModel.upper_eq]
    rw [hparent_lo, hchild_lo, hparent_size]
    change (a / k) * k + (k - 1) ≤ (a / k / 2) * (k * 2) + (k * 2 - 1)
    omega

theorem lower_eq_of_member_same_prefix (w a p x : Nat)
    (h : CidrModel.member w a p x) :
    CidrModel.lower w a p = CidrModel.lower w x p := by
  let k := CidrModel.size w p
  have hk : 0 < k := CidrModel.size_pos w p
  have hlow : (a / k) * k ≤ x := h.1
  have hupper : x ≤ (a / k) * k + k - 1 := by
    simpa [CidrModel.upper, CidrModel.lower, k] using h.2
  have hdiv : x / k = a / k := by
    rw [Nat.div_eq_iff hk]
    exact ⟨hlow, hupper⟩
  simp [CidrModel.lower, k, hdiv]

theorem parent_contains_child_iff_same_parent (a b p : Nat)
    (hpos : 0 < p) (hp : p ≤ 32) :
    CidrModel.subset 32 a (p - 1) b p ↔
      CidrModel.lower 32 a (p - 1) = CidrModel.lower 32 b (p - 1) := by
  constructor
  · intro hsub
    have hb : CidrModel.member 32 a (p - 1) b :=
      hsub b (CidrModel.address_mem 32 b p)
    exact lower_eq_of_member_same_prefix 32 a (p - 1) b hb
  · intro heq
    have hsub := parent_contains_child b p hpos hp
    intro x hx
    exact (CidrModel.member_eq_of_lower_eq 32 a b (p - 1) x heq).mpr
      (hsub x hx)

end IPv4NetMath
