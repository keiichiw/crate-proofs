import RangeJoinMinimal
open Aeneas Aeneas.Std Result
namespace join_regression
abbrev Bound := range_join_minimal.core.ops.range.Bound
abbrev RangeBounds := range_join_minimal.core.ops.range.RangeBounds

def withDefault (z : Usize) : Bound Usize → Usize
  | .Included n | .Excluded n => n
  | .Unbounded => z

abbrev value := withDefault 0#usize

-- Holds for arbitrary callbacks, including their Result effects/failure:
-- one start query followed, on success, by exactly one end query.
theorem exactly_two_queries {T} (R : RangeBounds T Usize) (r : T) (len : Usize) :
    range_join_minimal.trait_bound_twice R r len = (do
      let a ← R.start_bound r
      let b ← R.end_bound r
      .ok (value a,withDefault len b)) := by
  unfold range_join_minimal.trait_bound_twice
  congr 1
  funext a
  cases a <;> dsimp only [value,withDefault]
  all_goals congr 1; funext b; cases b <;> rfl

-- Choice preserves two sequential queries and their failure/divergence order.
theorem callback_paths_preserved {T} (R : RangeBounds T Usize) (r : T) (flag : Bool) :
    range_join_minimal.two_callback_paths R r flag = (do
      let a ← if flag then R.start_bound r else R.end_bound r
      let b ← if flag then R.end_bound r else R.start_bound r
      .ok (core.num.Usize.wrapping_add (value a) (value b))) := by
  cases flag <;> simp only [range_join_minimal.two_callback_paths,
    Bool.false_eq_true,ite_false,ite_true]
  all_goals congr 1; funext a; cases a <;> dsimp only [value,withDefault]
  all_goals congr 1; funext b; cases b <;> rfl

theorem mutable_path_values (x : Usize) (flag : Bool) :
    range_join_minimal.mutable_path x flag ⦃ out =>
      out = if flag then (11#usize,11#usize) else (21#usize,21#usize) ⦄ := by
  cases flag <;> unfold range_join_minimal.mutable_path <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  all_goals step; scalar_tac

theorem early_return_values (flag : Bool) :
    range_join_minimal.early_return flag = .ok (if flag then 7#usize else 9#usize) := by
  cases flag <;> rfl

theorem checked_path_success :
    range_join_minimal.checked_path false ⦃ out => out = 1#usize ⦄ := by
  unfold range_join_minimal.checked_path
  simp only [Bool.false_eq_true,ite_false]
  step
  scalar_tac

theorem checked_path_overflow (h64 : System.Platform.numBits = 64) :
    range_join_minimal.checked_path true = .fail .integerOverflow := by
  unfold range_join_minimal.checked_path
  change UScalar.add core.num.Usize.MAX 1#usize = _
  simp [core.num.Usize.MAX,UScalar.add,UScalar.tryMk,UScalar.tryMkOpt,
    Usize.max,UScalarTy.numBits,Usize.numBits,h64]

theorem break_path_values (flag : Bool) :
    range_join_minimal.break_path flag = .ok (if flag then 3#usize else 4#usize) := by
  cases flag <;> rfl

end join_regression
