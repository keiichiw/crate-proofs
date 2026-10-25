import Bytes
open Aeneas Aeneas.Std Result
namespace bytes
open buf.iter

theorem intoiter_new_spec {T : Type _} (inner : T) :
    ∃ out, IntoIter.new inner = .ok out ∧ out.inner = inner := by
  exact ⟨⟨inner⟩,rfl,rfl⟩
theorem intoiter_into_inner_spec {T : Type _} (s : IntoIter T) :
    ∃ out, IntoIter.into_inner s = .ok out ∧ out = s.inner := by
  exact ⟨s.inner,rfl,rfl⟩
theorem intoiter_get_ref_spec {T : Type _} (s : IntoIter T) :
    ∃ out, IntoIter.get_ref s = .ok out ∧ out = s.inner := by
  exact ⟨s.inner,rfl,rfl⟩
theorem intoiter_get_mut_spec {T : Type _} (s : IntoIter T) :
    ∃ out, IntoIter.get_mut s = .ok out ∧ out.1 = s.inner ∧
      (∀ replacement, (out.2 replacement).inner = replacement) := by
  exact ⟨(s.inner,fun replacement => {inner := replacement}),rfl,rfl,fun _ => rfl⟩
end bytes
