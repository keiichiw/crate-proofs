module
public import Proofs.OuterLoop

@[expose] public section
open Aeneas.Std Aeneas.Std.WP
namespace adler2

def split4Prelude (bytes : Slice U8) : Result (Slice U8 × Slice U8) := do
  let i := Slice.len bytes
  let i2 ← i % 4#usize
  let i3 ← i - i2
  core.slice.Slice.split_at bytes i3

theorem split4Prelude_spec (bytes : Slice U8) :
    ∃ pre rem : Slice U8,
      split4Prelude bytes = .ok (pre, rem) ∧
      pre.val ++ rem.val = bytes.val ∧
      pre.val.length % 4 = 0 ∧
      rem.val.length = bytes.val.length % 4 ∧
      rem.val.length < 4 := by
  let i := Slice.len bytes
  have hi : i.val = bytes.val.length := by
    simp [i]
  have hfour : (4#usize).val = 4 := by decide
  obtain ⟨i2, hi2, hi2val⟩ :=
    usize_rem_ok i 4#usize (by decide)
  have hi2le : i2.val ≤ i.val := by
    rw [hi2val]
    exact Nat.mod_le _ _
  obtain ⟨i3, hi3, hi3val⟩ := usize_sub_ok i i2 hi2le
  have hi3le : i3.val ≤ bytes.val.length := by
    rw [hi3val, hi]
    omega
  obtain ⟨p, hp, hspec⟩ :=
    spec_result_ok (core.slice.Slice.split_at.spec bytes i3 (by simpa using hi3le))
  rcases p with ⟨pre,rem⟩
  simp only [uncurry'_pair] at hspec
  rcases hspec with ⟨hpre, hrem, hpreval, hremval⟩
  refine ⟨pre,rem,?_,?_,?_,?_,?_⟩
  · simp [split4Prelude, hi2, hi3, hp, i]
  · rw [hpreval, hremval]
    exact List.take_append_drop _ _
  · rw [hpreval, List.length_take]
    simp [hi3val, hi2val, hi, hfour]
    omega
  · rw [hremval, List.length_drop, hi3val, hi2val, hi, hfour]
    omega
  · rw [hremval, List.length_drop, hi3val, hi2val, hi, hfour]
    omega

end adler2
