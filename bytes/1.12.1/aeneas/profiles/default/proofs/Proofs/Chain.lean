import Bytes
open Aeneas Aeneas.Std Result
namespace bytes
open buf.chain

def chainView {T U : Type _} (left : T → List U8) (right : U → List U8) (s : Chain T U) :=
  left s.a ++ right s.b

theorem chain_new_spec {T U : Type _} (left : T → List U8) (right : U → List U8) (a : T) (b : U) :
    ∃ out, Chain.new a b = .ok out ∧ out.a = a ∧ out.b = b ∧
      chainView left right out = left a ++ right b := by
  exact ⟨⟨a,b⟩,rfl,rfl,rfl,rfl⟩
theorem chain_first_ref_spec {T U : Type _} (s : Chain T U) :
    ∃ out, Chain.first_ref s = .ok out ∧ out = s.a := by
  exact ⟨s.a,rfl,rfl⟩
theorem chain_last_ref_spec {T U : Type _} (s : Chain T U) :
    ∃ out, Chain.last_ref s = .ok out ∧ out = s.b := by
  exact ⟨s.b,rfl,rfl⟩
theorem chain_into_inner_spec {T U : Type _} (s : Chain T U) :
    ∃ out, Chain.into_inner s = .ok out ∧ out = (s.a,s.b) := by
  exact ⟨(s.a,s.b),rfl,rfl⟩
theorem chain_first_mut_spec {T U : Type _} (left : T → List U8) (right : U → List U8) (s : Chain T U) :
    ∃ out, Chain.first_mut s = .ok out ∧ out.1 = s.a ∧
      (∀ replacement, (out.2 replacement).a = replacement ∧ (out.2 replacement).b = s.b ∧
        chainView left right (out.2 replacement) = left replacement ++ right s.b) := by
  exact ⟨(s.a,fun replacement => {s with a := replacement}),rfl,rfl,fun _ => ⟨rfl,rfl,rfl⟩⟩
theorem chain_last_mut_spec {T U : Type _} (left : T → List U8) (right : U → List U8) (s : Chain T U) :
    ∃ out, Chain.last_mut s = .ok out ∧ out.1 = s.b ∧
      (∀ replacement, (out.2 replacement).a = s.a ∧ (out.2 replacement).b = replacement ∧
        chainView left right (out.2 replacement) = left s.a ++ right replacement) := by
  exact ⟨(s.b,fun replacement => {s with b := replacement}),rfl,rfl,fun _ => ⟨rfl,rfl,rfl⟩⟩
end bytes
