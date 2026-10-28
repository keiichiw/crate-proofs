module
public import Proofs.IPv6RangeMath

public section

/-! Independent greedy dyadic partition model for a live, half-open IPv6
interval. The source iterator is deliberately not referenced here. -/
namespace IPv6SubnetMath

/-- A `/p` block beginning at `s` meets the requested minimum prefix,
address alignment, and the exclusive upper endpoint `t`. -/
@[expose] def eligible (s t q p : Nat) : Prop :=
  q ≤ p ∧ p ≤ 128 ∧ s % 2 ^ (128 - p) = 0 ∧ s + 2 ^ (128 - p) ≤ t

instance eligibleDecidable (s t q : Nat) : DecidablePred (eligible s t q) := by
  intro p
  unfold eligible
  infer_instance

theorem singleton_eligible (s t q : Nat) (hq : q ≤ 128) (hst : s < t) :
    eligible s t q 128 := by
  simp [eligible, hq]
  omega

theorem eligible_exists (s t q : Nat) (hq : q ≤ 128) (hst : s < t) :
    ∃ p, eligible s t q p :=
  ⟨128, singleton_eligible s t q hq hst⟩

/-- The least eligible prefix chooses the largest dyadic block. -/
@[expose] def bestPrefix (s t q : Nat) (hq : q ≤ 128) (hst : s < t) : Nat :=
  Nat.find (eligible_exists s t q hq hst)

theorem best_eligible (s t q : Nat) (hq : q ≤ 128) (hst : s < t) :
    eligible s t q (bestPrefix s t q hq hst) :=
  Nat.find_spec (eligible_exists s t q hq hst)

theorem best_le_of_eligible (s t q p : Nat) (hq : q ≤ 128) (hst : s < t)
    (hp : eligible s t q p) :
    bestPrefix s t q hq hst ≤ p :=
  Nat.find_min' (eligible_exists s t q hq hst) hp

/-- A concrete prefix matches the independent greedy choice exactly when it is
eligible and every shorter prefix fails one of the three constraints. -/
theorem best_eq_iff (s t q p : Nat) (hq : q ≤ 128) (hst : s < t) :
    bestPrefix s t q hq hst = p ↔
      eligible s t q p ∧ ∀ r < p, ¬ eligible s t q r := by
  exact Nat.find_eq_iff (eligible_exists s t q hq hst)

/-- Bridge criterion for an implementation that computes range and alignment
thresholds separately, then takes their maximum with `q`. -/
theorem best_eq_max_of_thresholds (s t q rangeThreshold alignThreshold : Nat)
    (hq : q ≤ 128) (hst : s < t)
    (hrange : ∀ p, p ≤ 128 →
      (rangeThreshold ≤ p ↔ s + 2 ^ (128-p) ≤ t))
    (halign : ∀ p, p ≤ 128 →
      (alignThreshold ≤ p ↔ s % 2 ^ (128-p) = 0)) :
    bestPrefix s t q hq hst =
      max (max rangeThreshold alignThreshold) q := by
  have hr128 : rangeThreshold ≤ 128 := by
    apply (hrange 128 (by omega)).2
    simpa using hst
  have ha128 : alignThreshold ≤ 128 := by
    apply (halign 128 (by omega)).2
    exact Nat.mod_one s
  let p := max (max rangeThreshold alignThreshold) q
  have hp128 : p ≤ 128 := by simp [p]; omega
  apply (best_eq_iff s t q p hq hst).2
  constructor
  · refine ⟨by simp [p], hp128, ?_, ?_⟩
    · apply (halign p hp128).1
      simp [p]
    · apply (hrange p hp128).1
      simp [p]
  · intro r hr her
    obtain ⟨hqr, hr128', har, hfit⟩ := her
    have hrr : rangeThreshold ≤ r := (hrange r hr128').2 hfit
    have hra : alignThreshold ≤ r := (halign r hr128').2 har
    simp [p] at hr
    omega

theorem best_bounds (s t q : Nat) (hq : q ≤ 128) (hst : s < t) :
    q ≤ bestPrefix s t q hq hst ∧ bestPrefix s t q hq hst ≤ 128 := by
  exact ⟨(best_eligible s t q hq hst).1,
    (best_eligible s t q hq hst).2.1⟩

/-- Astra's finite candidate set, expressed as dyadic height. -/
@[expose] def heightEligible (s t q h : Nat) : Prop :=
  h ≤ 128 - q ∧ 2 ^ h ∣ s ∧ s + 2 ^ h ≤ t

@[expose] def bestHeight (s t q : Nat) (hq : q ≤ 128) (hst : s < t) : Nat :=
  128 - bestPrefix s t q hq hst

theorem best_height_eligible (s t q : Nat) (hq : q ≤ 128) (hst : s < t) :
    heightEligible s t q (bestHeight s t q hq hst) := by
  obtain ⟨hqp, hp128, halign, hfit⟩ := best_eligible s t q hq hst
  refine ⟨by unfold bestHeight; omega, ?_, ?_⟩
  · exact Nat.dvd_of_mod_eq_zero halign
  · exact hfit

theorem height_le_best (s t q h : Nat) (hq : q ≤ 128)
    (hst : s < t) (hh : heightEligible s t q h) :
    h ≤ bestHeight s t q hq hst := by
  have hh128 : h ≤ 128 := by
    have := hh.1
    omega
  rcases hh with ⟨hBound, hDvd, hFit⟩
  let p := 128 - h
  have hp : eligible s t q p := by
    unfold eligible
    dsimp [p]
    have hexp : 128 - (128-h) = h := by omega
    change h ≤ 128 - q at hBound
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [hexp]
      exact Nat.mod_eq_zero_of_dvd hDvd
    · rw [hexp]
      exact hFit
  have hbest := best_le_of_eligible s t q p hq hst hp
  unfold bestHeight
  omega

/-- Numeric size of the selected subnet. -/
@[expose] def blockSize (s t q : Nat) (hq : q ≤ 128) (hst : s < t) : Nat :=
  2 ^ (128 - bestPrefix s t q hq hst)

theorem blockSize_pos (s t q : Nat) (hq : q ≤ 128) (hst : s < t) :
    0 < blockSize s t q hq hst := by
  simp [blockSize]

theorem block_fits (s t q : Nat) (hq : q ≤ 128) (hst : s < t) :
    s + blockSize s t q hq hst ≤ t := by
  exact (best_eligible s t q hq hst).2.2.2

theorem block_aligned (s t q : Nat) (hq : q ≤ 128) (hst : s < t) :
    s % blockSize s t q hq hst = 0 := by
  exact (best_eligible s t q hq hst).2.2.1

/-- No eligible block is larger than the selected one. -/
theorem eligible_size_le_best (s t q p : Nat) (hq : q ≤ 128)
    (hst : s < t) (hp : eligible s t q p) :
    2 ^ (128 - p) ≤ blockSize s t q hq hst := by
  unfold blockSize
  apply Nat.pow_le_pow_right (by omega : 0 < 2)
  have := best_le_of_eligible s t q p hq hst hp
  omega

theorem block_canonical (s t q : Nat) (hq : q ≤ 128) (hst : s < t) :
    CidrModel.lower 128 s (bestPrefix s t q hq hst) = s ∧
      CidrModel.upper 128 s (bestPrefix s t q hq hst) + 1 =
        s + blockSize s t q hq hst := by
  have halign := block_aligned s t q hq hst
  have hdecomp : s % blockSize s t q hq hst +
      (s / blockSize s t q hq hst) * blockSize s t q hq hst = s := by
    simpa [Nat.mul_comm] using Nat.mod_add_div s (blockSize s t q hq hst)
  have hlower : CidrModel.lower 128 s (bestPrefix s t q hq hst) = s := by
    simp only [CidrModel.lower, CidrModel.size]
    change (s / blockSize s t q hq hst) * blockSize s t q hq hst = s
    omega
  constructor
  · exact hlower
  · rw [CidrModel.upper_eq, hlower]
    have hpos := blockSize_pos s t q hq hst
    change s + (blockSize s t q hq hst - 1) + 1 =
      s + blockSize s t q hq hst
    omega

theorem block_membership (s t q x : Nat) (hq : q ≤ 128) (hst : s < t) :
    CidrModel.member 128 s (bestPrefix s t q hq hst) x ↔
      s ≤ x ∧ x < s + blockSize s t q hq hst := by
  obtain ⟨hlo, hhi⟩ := block_canonical s t q hq hst
  simp only [CidrModel.member, hlo]
  omega

/-- The residual address set after emitting `[s, s + blockSize)`. -/
@[expose] def residual (s t q : Nat) (hq : q ≤ 128) (hst : s < t) :
    RangeMath.HalfOpen :=
  if s + blockSize s t q hq hst < t then
    .live (s + blockSize s t q hq hst) t
  else .empty

theorem residual_partition (s t q x : Nat) (hq : q ≤ 128)
    (hst : s < t) :
    RangeMath.mem (.live s t) x ↔
      (s ≤ x ∧ x < s + blockSize s t q hq hst) ∨
      RangeMath.mem (residual s t q hq hst) x := by
  have hfit := block_fits s t q hq hst
  by_cases hmore : s + blockSize s t q hq hst < t
  · simp only [residual, hmore, ↓reduceIte, RangeMath.mem]
    omega
  · have heq : s + blockSize s t q hq hst = t := by omega
    simp only [residual, hmore, ↓reduceIte, RangeMath.mem]
    simp only [heq, or_false]

theorem residual_size (s t q : Nat) (hq : q ≤ 128) (hst : s < t) :
    RangeMath.size (residual s t q hq hst) +
      blockSize s t q hq hst = t - s := by
  have hfit := block_fits s t q hq hst
  by_cases hmore : s + blockSize s t q hq hst < t
  · simp only [residual, hmore, ↓reduceIte, RangeMath.size]
    omega
  · have heq : s + blockSize s t q hq hst = t := by omega
    simp only [residual, hmore, ↓reduceIte, RangeMath.size]
    omega

theorem residual_strictly_smaller (s t q : Nat) (hq : q ≤ 128)
    (hst : s < t) :
    RangeMath.size (residual s t q hq hst) < t - s := by
  have hs := residual_size s t q hq hst
  have hp := blockSize_pos s t q hq hst
  omega

theorem selected_endpoint_in_range (s t q : Nat) (hq : q ≤ 128)
    (hst : s < t) :
    s ≤ s + blockSize s t q hq hst - 1 ∧
      s + blockSize s t q hq hst - 1 < t := by
  have hfit := block_fits s t q hq hst
  have hpos := blockSize_pos s t q hq hst
  omega

theorem full_range_q0 :
    eligible 0 IPv6RangeMath.limit 0 0 := by
  simp [eligible, IPv6RangeMath.limit]

theorem zero_singleton_q128 : eligible 0 1 128 128 := by
  simp [eligible]

theorem max_singleton_q128 :
    eligible IPv6RangeMath.maxAddress IPv6RangeMath.limit 128 128 := by
  norm_num [eligible, IPv6RangeMath.maxAddress, IPv6RangeMath.limit]

theorem best_q128 (s t : Nat) (hst : s < t) :
    bestPrefix s t 128 (by omega) hst = 128 := by
  have hb := best_bounds s t 128 (by omega) hst
  omega

theorem full_range_best :
    bestPrefix 0 IPv6RangeMath.limit 0 (by omega)
      (by norm_num [IPv6RangeMath.limit]) = 0 := by
  have h := best_le_of_eligible 0 IPv6RangeMath.limit 0 0
    (by omega) (by norm_num [IPv6RangeMath.limit]) full_range_q0
  omega

end IPv6SubnetMath
