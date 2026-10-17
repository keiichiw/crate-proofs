module
public import Adler2

public section

open Aeneas.Std Aeneas.Std.WP

namespace adler2

/-- Total correctness of the failure-only result effect implies an exact successful result. -/
theorem spec_result_ok {α : Type _} {m : Result α} {p : α → Prop}
    (h : WP.spec m p) : ∃ value, m = Result.ok value ∧ p value := by
  cases m using Result.cases with
  | ret value =>
    exact ⟨value, rfl, WP.spec_ok value |>.mp h⟩
  | vis effect k =>
    exact False.elim ((WP.spec_vis effect k).mp h)
  | div =>
    exact False.elim (WP.spec_div.mp h)

theorem u32_add_ok (x y : U32) (h : x.val + y.val < 4294967296) :
    ∃ z : U32, (x + y) = Result.ok z ∧ z.val = x.val + y.val := by
  have hmax : x.val + y.val ≤ U32.max := by
    rw [U32.max_eq]
    omega
  exact spec_result_ok (U32.add_spec hmax)

theorem u32_mul_ok (x y : U32) (h : x.val * y.val < 4294967296) :
    ∃ z : U32, (x * y) = Result.ok z ∧ z.val = x.val * y.val := by
  have hmax : x.val * y.val ≤ U32.max := by
    rw [U32.max_eq]
    omega
  exact spec_result_ok (U32.mul_spec hmax)

theorem u32_rem_ok (x y : U32) (h : y.val ≠ 0) :
    ∃ z : U32, (x % y) = Result.ok z ∧ z.val = x.val % y.val :=
  spec_result_ok (U32.rem_spec x h)

theorem usize_rem_ok (x y : Usize) (h : y.val ≠ 0) :
    ∃ z : Usize, (x % y) = Result.ok z ∧ z.val = x.val % y.val :=
  spec_result_ok (Usize.rem_spec x h)

theorem usize_sub_ok (x y : Usize) (h : y.val ≤ x.val) :
    ∃ z : Usize, (x - y) = Result.ok z ∧ z.val = x.val - y.val := by
  obtain ⟨z, hz, hval, _⟩ := spec_result_ok (Usize.sub_spec h)
  exact ⟨z, hz, hval⟩

end adler2
