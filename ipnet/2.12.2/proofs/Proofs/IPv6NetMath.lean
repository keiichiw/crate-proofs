module
public import Proofs.RangeMath

public section

/-! Independent Nat arithmetic for the IPv6 network APIs. -/
namespace IPv6NetMath

@[expose] def limit : Nat := 2 ^ 128
@[expose] def maxAddress : Nat := limit - 1

@[expose] def hostStart (a p : Nat) : Nat :=
  CidrModel.lower 128 a p

@[expose] def hostStop (a p : Nat) : Nat :=
  CidrModel.upper 128 a p

@[expose] def hostsRemaining (a p : Nat) : RangeMath.HalfOpen :=
  RangeMath.ofInclusive (hostStart a p) (hostStop a p)

theorem maxAddress_eq : maxAddress = 2 ^ 128 - 1 := rfl

theorem host_endpoints_in_width (a p : Nat)
    (hp : p ≤ 128) (ha : a < IPv6NetMath.limit) :
    hostStart a p < IPv6NetMath.limit ∧ hostStop a p < IPv6NetMath.limit := by
  have hupper := CidrModel.upper_lt_width 128 a p hp
    (by simpa [IPv6NetMath.limit] using ha)
  have hlower := CidrModel.lower_le_upper 128 a p
  simpa [hostStart, hostStop, limit] using
    And.intro (lt_of_le_of_lt hlower hupper) hupper

theorem hosts_remaining_live (a p : Nat) :
    hostsRemaining a p =
      .live (CidrModel.lower 128 a p) (CidrModel.upper 128 a p + 1) := by
  have hle := CidrModel.lower_le_upper 128 a p
  simp [hostsRemaining, hostStart, hostStop, RangeMath.ofInclusive, hle]

theorem hosts_remaining_nonempty (a p : Nat) :
    hostsRemaining a p ≠ .empty := by
  rw [hosts_remaining_live]
  simp

theorem hosts_remaining_size (a p : Nat) :
    RangeMath.size (hostsRemaining a p) = CidrModel.size 128 p := by
  rw [hosts_remaining_live, CidrModel.upper_eq]
  simp only [RangeMath.size]
  have hk := CidrModel.size_pos 128 p
  omega

theorem hosts_remaining_zero (a : Nat) (ha : a < limit) :
    hostsRemaining a 0 = .live 0 limit := by
  rw [hosts_remaining_live]
  have hlo : CidrModel.lower 128 a 0 = 0 :=
    CidrModel.lower_zero 128 a (by simpa [limit] using ha)
  rw [CidrModel.upper_eq, hlo]
  simp [CidrModel.size, limit]

theorem hosts_remaining_full (a : Nat) :
    hostsRemaining a 128 = .live a (a + 1) := by
  rw [hosts_remaining_live]
  simp [CidrModel.lower_full, CidrModel.upper_eq, CidrModel.size]

/-- A valid /p block lies in its immediate /p-1 parent, even when the stored
    address has host bits. -/
theorem parent_contains_child (a p : Nat) (hpos : 0 < p) (hp : p ≤ 128) :
    CidrModel.subset 128 a (p - 1) a p := by
  let k := CidrModel.size 128 p
  have hk : 0 < k := CidrModel.size_pos 128 p
  have hparent_size : CidrModel.size 128 (p - 1) = k * 2 := by
    have he : 128 - (p - 1) = (128 - p) + 1 := by omega
    simp [CidrModel.size, k, he, pow_succ]
  have hparent_lo : CidrModel.lower 128 a (p - 1) =
      (a / k / 2) * (k * 2) := by
    simp only [CidrModel.lower, hparent_size]
    rw [← Nat.div_div_eq_div_mul]
  have hchild_lo : CidrModel.lower 128 a p = (a / k) * k := rfl
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
    (hpos : 0 < p) (hp : p ≤ 128) :
    CidrModel.subset 128 a (p - 1) b p ↔
      CidrModel.lower 128 a (p - 1) = CidrModel.lower 128 b (p - 1) := by
  constructor
  · intro hsub
    have hb : CidrModel.member 128 a (p - 1) b :=
      hsub b (CidrModel.address_mem 128 b p)
    exact lower_eq_of_member_same_prefix 128 a (p - 1) b hb
  · intro heq
    have hsub := parent_contains_child b p hpos hp
    intro x hx
    exact (CidrModel.member_eq_of_lower_eq 128 a b (p - 1) x heq).mpr
      (hsub x hx)

end IPv6NetMath
