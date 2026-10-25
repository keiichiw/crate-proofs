import Bytes
open Aeneas Aeneas.Std Result
namespace bytes
open buf.limit

def limitView {T : Type _} (view : T → List U8) (s : Limit T) : List U8 :=
  (view s.inner).take s.limit.val

theorem limit_new_spec {T : Type _} (view : T → List U8) (inner : T) (limit : Usize) :
    ∃ out, buf.limit.new inner limit = .ok out ∧
      out.inner = inner ∧ out.limit = limit ∧ limitView view out = (view inner).take limit.val := by
  exact ⟨⟨inner, limit⟩, rfl, rfl, rfl, rfl⟩

theorem limit_into_inner_spec {T : Type _} (s : Limit T) :
    ∃ out, Limit.into_inner s = .ok out ∧ out = s.inner := by
  exact ⟨s.inner, rfl, rfl⟩

theorem limit_get_ref_spec {T : Type _} (s : Limit T) :
    ∃ out, Limit.get_ref s = .ok out ∧ out = s.inner := by
  exact ⟨s.inner, rfl, rfl⟩

theorem limit_limit_spec {T : Type _} (s : Limit T) :
    ∃ out, Limit.impl.limit s = .ok out ∧ out = s.limit := by
  exact ⟨s.limit, rfl, rfl⟩

theorem limit_set_limit_spec {T : Type _} (view : T → List U8) (s : Limit T) (lim : Usize) :
    ∃ out, Limit.set_limit s lim = .ok out ∧ out.inner = s.inner ∧ out.limit = lim ∧
      limitView view out = (view s.inner).take lim.val := by
  exact ⟨{s with limit := lim}, rfl, rfl, rfl, rfl⟩

theorem limit_get_mut_spec {T : Type _} (view : T → List U8) (s : Limit T) :
    ∃ out, Limit.get_mut s = .ok out ∧ out.1 = s.inner ∧
      (∀ replacement, (out.2 replacement).inner = replacement ∧
        (out.2 replacement).limit = s.limit ∧
        limitView view (out.2 replacement) = (view replacement).take s.limit.val) := by
  exact ⟨(s.inner, fun replacement => {s with inner := replacement}), rfl, rfl,
    fun _ => ⟨rfl, rfl, rfl⟩⟩
end bytes
