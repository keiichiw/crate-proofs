module
public import Proofs.CidrModel

public section

/-! Independent integer interval facts for the IPv4 aggregate merge loop.
No theorem in this module is a claim about the extracted aggregate body. -/
namespace IPv4AggregateMath

@[expose] def inInterval (lo hi x : Nat) : Prop := lo ≤ x ∧ x ≤ hi

/-- For a sorted incoming interval, the source's overlap-or-adjacency test
allows replacing the old end by `max` without changing the represented set. -/
theorem merge_union (lo oldHi newLo newHi x : Nat)
    (hsorted : lo ≤ newLo) (htouch : newLo ≤ oldHi + 1) :
    inInterval lo (max oldHi newHi) x ↔
      inInterval lo oldHi x ∨ inInterval newLo newHi x := by
  unfold inInterval
  constructor
  · intro hx
    by_cases hleft : x ≤ oldHi
    · exact Or.inl ⟨hx.1, hleft⟩
    · have hright : x ≤ newHi := by
        have := hx.2
        omega
      exact Or.inr ⟨by omega, hright⟩
  · intro hx
    rcases hx with hleft | hright
    · exact ⟨hleft.1, le_trans hleft.2 (Nat.le_max_left _ _)⟩
    · exact ⟨le_trans hsorted hright.1,
        le_trans hright.2 (Nat.le_max_right _ _)⟩

/-- With bounded IPv4 endpoints, `saturating_add(1)` has exactly the same
truth value in the aggregate test as mathematical adjacency. -/
theorem saturated_touch_iff (oldHi newLo : Nat)
    (hnew : newLo ≤ 2 ^ 32 - 1) :
    newLo ≤ min (2 ^ 32 - 1) (oldHi + 1) ↔ newLo ≤ oldHi + 1 := by
  constructor
  · intro h
    exact le_trans h (min_le_right _ _)
  · intro h
    exact le_min hnew h

/-- The non-touch branch leaves a strict address gap and cannot overlap the
previous interval. -/
theorem separated (lo oldHi newLo newHi x : Nat)
    (hgap : oldHi + 1 < newLo) :
    inInterval lo oldHi x → ¬ inInterval newLo newHi x := by
  unfold inInterval
  intro hx hy
  omega

theorem separated_order (oldHi newLo : Nat)
    (hgap : oldHi + 1 < newLo) : oldHi < newLo := by
  omega

end IPv4AggregateMath
