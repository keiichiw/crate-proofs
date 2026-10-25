import Aeneas
open Aeneas Aeneas.Std
namespace bytes_tool
/-- Preserve every observable effect/divergence of a computation whose successful
result is uninhabited; the added unreachable continuation cannot be called. -/
theorem never_continuation_exact {α : Type _} (m : Result Never) :
    (m >>= fun _ => (Result.fail .panic : Result α)) =
      (m >>= fun impossible => nomatch impossible) := by
  have h : (fun _ : Never => (Result.fail .panic : Result α)) =
      (fun impossible : Never => (nomatch impossible : Result α)) := by
    funext impossible
    cases impossible
  rw [h]

end bytes_tool
