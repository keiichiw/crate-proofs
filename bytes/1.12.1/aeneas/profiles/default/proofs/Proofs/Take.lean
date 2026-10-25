import Bytes
open Aeneas Aeneas.Std Result
namespace bytes
open buf.take

def visible {T : Type _} (view : T → List U8) (s : Take T) : List U8 :=
  (view s.inner).take s.limit.val

theorem take_new_spec {T : Type _} (view : T → List U8) (inner : T) (limit : Usize) :
    ∃ out, buf.take.new inner limit = .ok out ∧
      out.inner = inner ∧ out.limit = limit ∧ visible view out = (view inner).take limit.val := by
  exact ⟨⟨inner, limit⟩, rfl, rfl, rfl, rfl⟩

theorem take_into_inner_spec {T : Type _} (s : Take T) :
    ∃ out, Take.into_inner s = .ok out ∧ out = s.inner := by
  exact ⟨s.inner, rfl, rfl⟩

theorem take_get_ref_spec {T : Type _} (s : Take T) :
    ∃ out, Take.get_ref s = .ok out ∧ out = s.inner := by
  exact ⟨s.inner, rfl, rfl⟩

theorem take_limit_spec {T : Type _} (s : Take T) :
    ∃ out, Take.impl.limit s = .ok out ∧ out = s.limit := by
  exact ⟨s.limit, rfl, rfl⟩

theorem take_set_limit_spec {T : Type _} (view : T → List U8) (s : Take T) (lim : Usize) :
    ∃ out, Take.set_limit s lim = .ok out ∧ out.inner = s.inner ∧ out.limit = lim ∧
      visible view out = (view s.inner).take lim.val := by
  exact ⟨{s with limit := lim}, rfl, rfl, rfl, rfl⟩

theorem take_get_mut_spec {T : Type _} (view : T → List U8) (s : Take T) :
    ∃ out, Take.get_mut s = .ok out ∧ out.1 = s.inner ∧
      (∀ replacement, (out.2 replacement).inner = replacement ∧
        (out.2 replacement).limit = s.limit ∧
        visible view (out.2 replacement) = (view replacement).take s.limit.val) := by
  exact ⟨(s.inner, fun replacement => {s with inner := replacement}), rfl, rfl,
    fun _ => ⟨rfl, rfl, rfl⟩⟩
end bytes
