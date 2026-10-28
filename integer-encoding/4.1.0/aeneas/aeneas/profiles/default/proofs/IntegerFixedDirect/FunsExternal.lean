module
public import Aeneas
public import IntegerFixedDirect.Types
@[expose] public section
open Aeneas Aeneas.Std Result

namespace IntegerFixedDirect

/-- Reviewed standard-library supplement. Size is specified only for the selected
    builtin scalar domains. Cardinality selects their bit width, not general Rust
    layout: no correctness claim for other types, including other finite types. -/
noncomputable def core.mem.size_of (T : Type _) : Result Usize := by
  classical
  exact if Nat.card T = 2^8 then .ok 1#usize
    else if Nat.card T = 2^16 then .ok 2#usize
    else if Nat.card T = 2^32 then .ok 4#usize
    else if Nat.card T = 2^64 then .ok 8#usize
    else .fail .panic

/-- Standard byte-slice cloning: only instantiated with U8 and its standard Clone.
    Unsupported element types are deliberately outside the claimed model domain. -/
noncomputable def core.slice.Slice.clone_from_slice {T : Type _}
    (_clone : Aeneas.Std.core.clone.Clone T) (dst src : Slice T) : Result (Slice T) := by
  classical
  exact if T = U8 ∧ dst.val.length = src.val.length then .ok src else .fail .panic

/-- Pointer-sized byte operations are modeled for the extracted x86_64 target.
    Public pointer-sized correctness contracts must require Platform.numBits=64. -/
def core.num.Usize.to_le_bytes (x : Usize) : Array U8 8#usize :=
  Aeneas.Std.core.num.U64.to_le_bytes ⟨x.bv.setWidth 64⟩
def core.num.Usize.to_be_bytes (x : Usize) : Array U8 8#usize :=
  Aeneas.Std.core.num.U64.to_be_bytes ⟨x.bv.setWidth 64⟩
def core.num.Usize.from_le_bytes (a : Array U8 8#usize) : Usize :=
  ⟨(Aeneas.Std.core.num.U64.from_le_bytes a).bv.setWidth UScalarTy.Usize.numBits⟩
def core.num.Isize.to_le_bytes (x : Isize) : Array U8 8#usize :=
  Aeneas.Std.core.num.I64.to_le_bytes ⟨x.bv.setWidth 64⟩
def core.num.Isize.to_be_bytes (x : Isize) : Array U8 8#usize :=
  Aeneas.Std.core.num.I64.to_be_bytes ⟨x.bv.setWidth 64⟩
def core.num.Isize.from_le_bytes (a : Array U8 8#usize) : Isize :=
  ⟨(Aeneas.Std.core.num.I64.from_le_bytes a).bv.setWidth IScalarTy.Isize.numBits⟩

/-- The standard unwrap model does not use its Debug dictionary. Erase that
    formatting-only dictionary for the selected TryFromSliceError instance;
    panic messages are not observations of the Aeneas Result semantics. -/
def core.fmt.DebugTryFromSliceError : Unit := ()
def core.result.Result.unwrap {T : Type _} (_debug : Unit)
    (r : Aeneas.Std.core.result.Result T Aeneas.Std.core.array.TryFromSliceError) : Result T :=
  match r with
  | .Ok x => .ok x
  | .Err _ => .fail .panic

end IntegerFixedDirect
