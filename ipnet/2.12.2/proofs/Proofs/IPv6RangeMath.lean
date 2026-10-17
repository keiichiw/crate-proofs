module
public import Proofs.RangeMath

public section

/-! Independent Nat model of the inclusive IPv6 range iterator. Numeric state
is raw `(start,end)`; `(1,0)` is the source iterator's exhausted sentinel.
The full range has cardinality `2^128`, represented here without overflow. -/
namespace IPv6RangeMath

@[expose] def limit : Nat := 2 ^ 128
@[expose] def maxAddress : Nat := limit - 1
@[expose] def usizeLimit : Nat := 2 ^ 64
@[expose] def usizeMax : Nat := usizeLimit - 1

@[expose] def card (s e : Nat) : Nat :=
  if s ≤ e then e + 1 - s else 0

@[expose] def remaining (s e : Nat) : RangeMath.HalfOpen :=
  RangeMath.ofInclusive s e

/-- The checked `u128` count is unavailable only for a range too large for u128. -/
@[expose] def countU128 (s e : Nat) : Option Nat :=
  if card s e < limit then some (card s e) else none

@[expose] def sizeHint (s e : Nat) : Nat × Option Nat :=
  let c := card s e
  if c ≤ usizeMax then (c, some c) else (usizeMax, none)

/-- `none` denotes the modeled integer-overflow failure of public `count`. -/
@[expose] def countNormal (s e : Nat) : Option Nat :=
  if card s e ≤ usizeMax then some (card s e) else none

/-- `nth` outcome: optional value, then raw stored start/end. -/
@[expose] def nth (s e n : Nat) : Option Nat × Nat × Nat :=
  let c := card s e
  if c ≤ n then (none, 1, 0)
  else if n + 1 = c then (some e, 1, 0)
  else (some (s + n), s + n + 1, e)

/-- `nth_back` outcome: optional value, then raw stored start/end. -/
@[expose] def nthBack (s e n : Nat) : Option Nat × Nat × Nat :=
  let c := card s e
  if c ≤ n then (none, 1, 0)
  else if n + 1 = c then (some s, 1, 0)
  else (some (e - n), s, e - n - 1)

theorem limit_pos : 0 < limit := by norm_num [limit]
theorem usize_limit_pos : 0 < usizeLimit := by norm_num [usizeLimit]
theorem usize_limit_lt_limit : usizeLimit < limit := by
  norm_num [usizeLimit, limit]

theorem card_empty (s e : Nat) (h : e < s) : card s e = 0 := by
  simp [card, Nat.not_le.mpr h]

theorem card_live (s e : Nat) (h : s ≤ e) : card s e = e + 1 - s := by
  simp [card, h]

theorem card_pos (s e : Nat) (h : s ≤ e) : 0 < card s e := by
  rw [card_live _ _ h]
  omega

theorem card_le_limit (s e : Nat) (_hs : s < limit) (he : e < limit) :
    card s e ≤ limit := by
  by_cases h : s ≤ e
  · rw [card_live _ _ h]
    omega
  · have h' : e < s := by omega
    simp [card_empty _ _ h']

theorem card_eq_limit_iff_full (s e : Nat)
    (hs : s < limit) (he : e < limit) :
    card s e = limit ↔ s = 0 ∧ e = maxAddress := by
  constructor
  · intro hc
    by_cases h : s ≤ e
    · rw [card_live _ _ h] at hc
      have hmax : e ≤ maxAddress := by simp [maxAddress]; omega
      have : e = maxAddress ∧ s = 0 := by
        simp [maxAddress] at hmax ⊢
        omega
      exact ⟨this.2, this.1⟩
    · have h' : e < s := by omega
      rw [card_empty _ _ h'] at hc
      have := limit_pos
      omega
  · rintro ⟨rfl, rfl⟩
    have hm : 0 ≤ maxAddress := Nat.zero_le _
    rw [card_live _ _ hm]
    have hl := limit_pos
    simp only [maxAddress]
    omega

theorem countU128_some_iff (s e c : Nat)
    (hs : s < limit) (he : e < limit) :
    countU128 s e = some c ↔ c = card s e ∧ ¬ (s = 0 ∧ e = maxAddress) := by
  have hle := card_le_limit s e hs he
  have hfull := card_eq_limit_iff_full s e hs he
  constructor
  · intro h
    by_cases hlt : card s e < limit
    · have hc : card s e = c := by
        simpa [countU128, hlt] using h
      refine ⟨hc.symm, ?_⟩
      intro hf
      have : card s e = limit := hfull.mpr hf
      omega
    · simp [countU128, hlt] at h
  · rintro ⟨rfl, hnot⟩
    have hlt : card s e < limit := by
      by_contra hn
      have heq : card s e = limit := by omega
      exact hnot (hfull.mp heq)
    simp [countU128, hlt]

theorem sizeHint_exact (s e : Nat) (h : card s e ≤ usizeMax) :
    sizeHint s e = (card s e, some (card s e)) := by
  simp [sizeHint, h]

theorem countNormal_some_iff (s e c : Nat) :
    countNormal s e = some c ↔ c = card s e ∧ card s e ≤ usizeMax := by
  by_cases h : card s e ≤ usizeMax
  · simp [countNormal, h, eq_comm]
  · simp [countNormal, h]

theorem countNormal_none_iff (s e : Nat) :
    countNormal s e = none ↔ usizeMax < card s e := by
  by_cases h : card s e ≤ usizeMax
  · simp [countNormal, h, Nat.not_lt.mpr h]
  · have h' : usizeMax < card s e := by omega
    simp [countNormal, h, h']

theorem sizeHint_overflow (s e : Nat) (h : usizeMax < card s e) :
    sizeHint s e = (usizeMax, none) := by
  have hn : ¬ card s e ≤ usizeMax := by omega
  simp [sizeHint, hn]

theorem sizeHint_full : sizeHint 0 maxAddress = (usizeMax, none) := by
  have hcard : card 0 maxAddress = limit := by
    have hm : maxAddress < limit := by
      unfold maxAddress
      have hp := limit_pos
      omega
    exact (card_eq_limit_iff_full 0 maxAddress (by exact limit_pos) hm).mpr
      ⟨rfl, rfl⟩
  apply sizeHint_overflow
  rw [hcard]
  have hlt := usize_limit_lt_limit
  simp [usizeMax] at *
  omega

theorem nth_out_of_bounds (s e n : Nat) (h : card s e ≤ n) :
    nth s e n = (none, 1, 0) := by simp [nth, h]

theorem nth_last (s e n : Nat) (h : n + 1 = card s e) :
    nth s e n = (some e, 1, 0) := by
  have hlt : ¬ card s e ≤ n := by omega
  simp [nth, hlt, h]

theorem nth_middle (s e n : Nat)
    (h : n + 1 < card s e) :
    nth s e n = (some (s + n), s + n + 1, e) := by
  have hlt : ¬ card s e ≤ n := by omega
  have hne : n + 1 ≠ card s e := by omega
  simp [nth, hlt, hne]

theorem nthBack_out_of_bounds (s e n : Nat) (h : card s e ≤ n) :
    nthBack s e n = (none, 1, 0) := by simp [nthBack, h]

theorem nthBack_last (s e n : Nat) (h : n + 1 = card s e) :
    nthBack s e n = (some s, 1, 0) := by
  have hlt : ¬ card s e ≤ n := by omega
  simp [nthBack, hlt, h]

theorem nthBack_middle (s e n : Nat)
    (h : n + 1 < card s e) :
    nthBack s e n = (some (e - n), s, e - n - 1) := by
  have hlt : ¬ card s e ≤ n := by omega
  have hne : n + 1 ≠ card s e := by omega
  simp [nthBack, hlt, hne]

theorem nth_middle_card (s e n : Nat) (h : n + 1 < card s e) :
    card (s + n + 1) e = card s e - (n + 1) := by
  have hse : s ≤ e := by
    by_contra hn
    have he : e < s := by omega
    rw [card_empty _ _ he] at h
    omega
  have hnew : s + n + 1 ≤ e := by
    rw [card_live _ _ hse] at h
    omega
  rw [card_live _ _ hnew, card_live _ _ hse]
  omega

theorem nthBack_middle_card (s e n : Nat) (h : n + 1 < card s e) :
    card s (e - n - 1) = card s e - (n + 1) := by
  have hse : s ≤ e := by
    by_contra hn
    have he : e < s := by omega
    rw [card_empty _ _ he] at h
    omega
  have hcard : card s e = e + 1 - s := card_live _ _ hse
  rw [hcard] at h
  have hnew : s ≤ e - n - 1 := by
    omega
  have hnle : n + 1 ≤ e := by omega
  rw [card_live _ _ hnew, card_live _ _ hse]
  omega

theorem countU128_full : countU128 0 maxAddress = none := by
  have hm : maxAddress < limit := by
    have hp := limit_pos
    unfold maxAddress
    omega
  have hc := (card_eq_limit_iff_full 0 maxAddress limit_pos hm).mpr ⟨rfl, rfl⟩
  simp [countU128, hc]

theorem nth_full (n : Nat) (hn : n < usizeLimit) :
    nth 0 maxAddress n = (some n, n + 1, maxAddress) := by
  have hm : maxAddress < limit := by
    have hp := limit_pos
    unfold maxAddress
    omega
  have hc := (card_eq_limit_iff_full 0 maxAddress limit_pos hm).mpr ⟨rfl, rfl⟩
  have hmiddle : n + 1 < card 0 maxAddress := by
    rw [hc]
    have hu := usize_limit_lt_limit
    omega
  simpa using nth_middle 0 maxAddress n hmiddle

theorem nthBack_full (n : Nat) (hn : n < usizeLimit) :
    nthBack 0 maxAddress n =
      (some (maxAddress - n), 0, maxAddress - n - 1) := by
  have hm : maxAddress < limit := by
    have hp := limit_pos
    unfold maxAddress
    omega
  have hc := (card_eq_limit_iff_full 0 maxAddress limit_pos hm).mpr ⟨rfl, rfl⟩
  have hmiddle : n + 1 < card 0 maxAddress := by
    rw [hc]
    have hu := usize_limit_lt_limit
    omega
  simpa using nthBack_middle 0 maxAddress n hmiddle

theorem exhausted_remaining : remaining 1 0 = .empty := by
  simp [remaining, RangeMath.ofInclusive]

theorem nth_no_revival (n m : Nat) :
    nth 1 0 n = (none, 1, 0) ∧ nthBack 1 0 m = (none, 1, 0) := by
  simp [nth, nthBack, card_empty 1 0 (by omega)]

end IPv6RangeMath
