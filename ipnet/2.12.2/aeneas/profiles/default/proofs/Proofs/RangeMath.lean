module
public import Proofs.CidrModel

public section

/-! Independent natural-number model of inclusive IPv4 address ranges and
    their canonical half-open representation. No extracted iterator body is
    referenced by this module. -/
namespace RangeMath

@[expose] def limit : Nat := 2 ^ 32
@[expose] def maxAddress : Nat := limit - 1

inductive HalfOpen where
  | empty
  | live (lo hi : Nat)
deriving DecidableEq, Repr

@[expose] def ofInclusive (start stop : Nat) : HalfOpen :=
  if start ≤ stop then .live start (stop + 1) else .empty

@[expose] def mem : HalfOpen → Nat → Prop
  | .empty, _ => False
  | .live lo hi, x => lo ≤ x ∧ x < hi

@[expose] def size : HalfOpen → Nat
  | .empty => 0
  | .live lo hi => hi - lo

/-- Saturating increment of a valid IPv4 numeric address. -/
@[expose] def saturatingSucc (a : Nat) : Nat := min (a + 1) maxAddress

/-- One logical iterator step on the half-open representation. -/
@[expose] def next : HalfOpen → Option Nat × HalfOpen
  | .empty => (none, .empty)
  | .live lo hi =>
      if lo < hi then
        (some lo, if lo + 1 < hi then .live (lo + 1) hi else .empty)
      else (none, .empty)

theorem ofInclusive_empty_iff (start stop : Nat) :
    ofInclusive start stop = .empty ↔ stop < start := by
  simp [ofInclusive]

theorem ofInclusive_live_iff (start stop lo hi : Nat) :
    ofInclusive start stop = .live lo hi ↔
      start ≤ stop ∧ lo = start ∧ hi = stop + 1 := by
  by_cases h : start ≤ stop
  · simp [ofInclusive, h, eq_comm]
  · simp [ofInclusive, h]

theorem mem_ofInclusive_iff (start stop x : Nat) :
    mem (ofInclusive start stop) x ↔ start ≤ x ∧ x ≤ stop := by
  by_cases h : start ≤ stop
  · simp only [ofInclusive, h, ↓reduceIte, mem]
    omega
  · have hn : ¬ (start ≤ x ∧ x ≤ stop) := by omega
    simp [ofInclusive, h, mem, hn]

theorem size_ofInclusive (start stop : Nat) :
    size (ofInclusive start stop) =
      if start ≤ stop then stop + 1 - start else 0 := by
  by_cases h : start ≤ stop <;> simp [ofInclusive, size, h]

theorem endpoint_le_limit (stop : Nat) (hstop : stop < limit) :
    stop + 1 ≤ limit := by omega

theorem live_bounds (start stop : Nat)
    (_hstart : start < limit) (hstop : stop < limit) (h : start ≤ stop) :
    ofInclusive start stop = .live start (stop + 1) ∧
      start < stop + 1 ∧ stop + 1 ≤ limit := by
  constructor
  · simp [ofInclusive, h]
  constructor
  · omega
  · exact endpoint_le_limit stop hstop

theorem maxAddress_eq : maxAddress = 4294967295 := by
  norm_num [maxAddress, limit]

theorem saturatingSucc_lt (start stop : Nat)
    (hstart : start < stop) (hstop : stop < limit) :
    saturatingSucc start = start + 1 := by
  have hm : start + 1 ≤ maxAddress := by
    rw [maxAddress_eq]
    norm_num [limit] at hstop
    omega
  simp [saturatingSucc, Nat.min_eq_left hm]

theorem saturatingSucc_max : saturatingSucc maxAddress = maxAddress := by
  simp [saturatingSucc]

theorem next_lt (start stop : Nat) (h : start < stop) :
    next (ofInclusive start stop) =
      (some start, ofInclusive (start + 1) stop) := by
  have hle : start ≤ stop := Nat.le_of_lt h
  have hsucc : start + 1 ≤ stop := h
  simp [next, ofInclusive, hle, hsucc]

theorem next_eq (start : Nat) :
    next (ofInclusive start start) = (some start, .empty) := by
  simp [next, ofInclusive]

theorem next_gt (start stop : Nat) (h : stop < start) :
    next (ofInclusive start stop) = (none, .empty) := by
  simp [next, ofInclusive, Nat.not_le.mpr h]

/-- The Rust equality-branch sentinel `(1, 0)` denotes the empty range. -/
theorem sentinel_empty : ofInclusive 1 0 = .empty := by
  rfl

theorem next_eq_sentinel (start : Nat) :
    next (ofInclusive start start) = (some start, ofInclusive 1 0) := by
  rw [next_eq, sentinel_empty]

theorem next_none_iff (start stop : Nat) :
    (next (ofInclusive start stop)).1 = none ↔ stop < start := by
  by_cases h : stop < start
  · simp [next_gt start stop h, h]
  · have hle : start ≤ stop := by omega
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · simp [next_lt start stop hlt, h]
    · subst stop
      simp [next_eq]

theorem next_some_size (start stop : Nat) (h : start ≤ stop) :
    (next (ofInclusive start stop)).1 = some start ∧
      size (next (ofInclusive start stop)).2 + 1 =
        size (ofInclusive start stop) := by
  rcases Nat.lt_or_eq_of_le h with hlt | heq
  · rw [next_lt start stop hlt]
    constructor
    · rfl
    · simp [size_ofInclusive, h, hlt]
      omega
  · subst stop
    rw [next_eq]
    constructor
    · rfl
    · change 1 = size (ofInclusive start start)
      rw [size_ofInclusive]
      simp

theorem next_partition (start stop x : Nat) (h : start ≤ stop) :
    mem (ofInclusive start stop) x ↔
      x = start ∨ mem (next (ofInclusive start stop)).2 x := by
  rw [mem_ofInclusive_iff]
  rcases Nat.lt_or_eq_of_le h with hlt | heq
  · rw [next_lt start stop hlt]
    rw [mem_ofInclusive_iff]
    omega
  · subst stop
    rw [next_eq]
    simp [mem]
    omega

theorem next_residual_excludes_head (start stop : Nat) (h : start ≤ stop) :
    ¬ mem (next (ofInclusive start stop)).2 start := by
  rcases Nat.lt_or_eq_of_le h with hlt | heq
  · rw [next_lt start stop hlt]
    rw [mem_ofInclusive_iff]
    omega
  · subst stop
    simp [next_eq, mem]

theorem next_empty : next .empty = (none, .empty) := rfl

@[expose] def advance : Nat → HalfOpen → HalfOpen
  | 0, r => r
  | n + 1, r => advance n (next r).2

theorem advance_empty (n : Nat) : advance n .empty = .empty := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [advance, next_empty] using ih

theorem full_range : ofInclusive 0 maxAddress = .live 0 limit := by
  norm_num [ofInclusive, maxAddress, limit]

theorem zero_singleton_step :
    next (ofInclusive 0 0) = (some 0, .empty) := next_eq 0

theorem max_singleton_step :
    next (ofInclusive maxAddress maxAddress) =
      (some maxAddress, .empty) := next_eq maxAddress

theorem full_range_step :
    next (ofInclusive 0 maxAddress) = (some 0, .live 1 limit) := by
  rw [full_range]
  norm_num [next, limit]

end RangeMath
