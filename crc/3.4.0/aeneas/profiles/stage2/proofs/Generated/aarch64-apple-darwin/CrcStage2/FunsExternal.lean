module
public import CrcStage2.Types
@[expose] public section
open Aeneas Aeneas.Std Result
namespace CrcStage2
/-- Runtime model of Rust's bit-reversal intrinsic on its five unsigned scalar domains. -/
noncomputable def core.intrinsics.bitreverse
    {T : Type} (_ : core.marker.Copy T) (x : T) : Result T := by
  classical
  exact if h : T = U8 then
    .ok (h.symm ▸ (⟨(h ▸ x : U8).bv.reverse⟩ : U8))
  else if h : T = U16 then
    .ok (h.symm ▸ (⟨(h ▸ x : U16).bv.reverse⟩ : U16))
  else if h : T = U32 then
    .ok (h.symm ▸ (⟨(h ▸ x : U32).bv.reverse⟩ : U32))
  else if h : T = U64 then
    .ok (h.symm ▸ (⟨(h ▸ x : U64).bv.reverse⟩ : U64))
  else if h : T = U128 then
    .ok (h.symm ▸ (⟨(h ▸ x : U128).bv.reverse⟩ : U128))
  else .fail .panic
end CrcStage2
