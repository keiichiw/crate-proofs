import IntegerFixedVec
import FixedProofs
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace IntegerFixedVecProofs

/-- Only these two fields are read by the extracted inherited method.
    All other dictionary fields remain arbitrary and are not trusted. -/
def specialize {T : Type} {N : Usize}
    (d : integer_encoding.fixed.FixedInt T (Array U8 N))
    (light : T → Result (Array U8 N)) : integer_encoding.fixed.FixedInt T (Array U8 N) :=
  { d with
    encode_fixed_light := light
    coreconvertAsRefSelf_BytesSliceU8Inst := Array.Insts.CoreConvertAsRefSlice U8 N }

theorem generic_total {T : Type} {N : Usize}
    (d : integer_encoding.fixed.FixedInt T (Array U8 N)) (light : T → Result (Array U8 N))
    (value : T) (bytes : List Nat)
    (hlight : ∃ out, light value = .ok out ∧ out.val.map (fun b => b.val) = bytes) :
    ∃ out, integer_encoding.fixed.FixedInt.encode_fixed_vec.default (specialize d light) value = .ok out ∧
      out.val.map (fun b => b.val) = bytes := by
  apply IntegerRequiredSpace.total_result
  unfold integer_encoding.fixed.FixedInt.encode_fixed_vec.default specialize
  obtain ⟨a,ha,hbytes⟩ := hlight
  simp only [ha,bind_ok]
  step
  apply WP.spec_mono (alloc.slice.Slice.to_vec_spec core.clone.CloneU8 s (by intros; rfl))
  intro out hout
  change out.slice.val.map (fun b => b.val) = bytes
  rw [← hout,s_post]
  exact hbytes

theorem u8_total (d : integer_encoding.fixed.FixedInt U8 (Array U8 1#usize)) (x : U8) :
    ∃ out, integer_encoding.fixed.FixedInt.encode_fixed_vec.default
      (specialize d IntegerFixedDirect.U8.Insts.Integer_encodingFixedFixedIntArrayU81.encode_fixed_light) x = .ok out ∧
      out.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 1 x.bv.toNat := by
  exact generic_total d _ x _ (IntegerFixedProofs.u8_light x)

theorem u16_total (d : integer_encoding.fixed.FixedInt U16 (Array U8 2#usize)) (x : U16) :
    ∃ out, integer_encoding.fixed.FixedInt.encode_fixed_vec.default
      (specialize d IntegerFixedDirect.U16.Insts.Integer_encodingFixedFixedIntArrayU82.encode_fixed_light) x = .ok out ∧
      out.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 2 x.bv.toNat := by
  exact generic_total d _ x _ (IntegerFixedProofs.u16_light x)

theorem u32_total (d : integer_encoding.fixed.FixedInt U32 (Array U8 4#usize)) (x : U32) :
    ∃ out, integer_encoding.fixed.FixedInt.encode_fixed_vec.default
      (specialize d IntegerFixedDirect.U32.Insts.Integer_encodingFixedFixedIntArrayU84.encode_fixed_light) x = .ok out ∧
      out.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 4 x.bv.toNat := by
  exact generic_total d _ x _ (IntegerFixedProofs.u32_light x)

theorem u64_total (d : integer_encoding.fixed.FixedInt U64 (Array U8 8#usize)) (x : U64) :
    ∃ out, integer_encoding.fixed.FixedInt.encode_fixed_vec.default
      (specialize d IntegerFixedDirect.U64.Insts.Integer_encodingFixedFixedIntArrayU88.encode_fixed_light) x = .ok out ∧
      out.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 8 x.bv.toNat := by
  exact generic_total d _ x _ (IntegerFixedProofs.u64_light x)

theorem i8_total (d : integer_encoding.fixed.FixedInt I8 (Array U8 1#usize)) (x : I8) :
    ∃ out, integer_encoding.fixed.FixedInt.encode_fixed_vec.default
      (specialize d IntegerFixedDirect.I8.Insts.Integer_encodingFixedFixedIntArrayU81.encode_fixed_light) x = .ok out ∧
      out.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 1 x.bv.toNat := by
  exact generic_total d _ x _ (IntegerFixedProofs.i8_light x)

theorem i16_total (d : integer_encoding.fixed.FixedInt I16 (Array U8 2#usize)) (x : I16) :
    ∃ out, integer_encoding.fixed.FixedInt.encode_fixed_vec.default
      (specialize d IntegerFixedDirect.I16.Insts.Integer_encodingFixedFixedIntArrayU82.encode_fixed_light) x = .ok out ∧
      out.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 2 x.bv.toNat := by
  exact generic_total d _ x _ (IntegerFixedProofs.i16_light x)

theorem i32_total (d : integer_encoding.fixed.FixedInt I32 (Array U8 4#usize)) (x : I32) :
    ∃ out, integer_encoding.fixed.FixedInt.encode_fixed_vec.default
      (specialize d IntegerFixedDirect.I32.Insts.Integer_encodingFixedFixedIntArrayU84.encode_fixed_light) x = .ok out ∧
      out.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 4 x.bv.toNat := by
  exact generic_total d _ x _ (IntegerFixedProofs.i32_light x)

theorem i64_total (d : integer_encoding.fixed.FixedInt I64 (Array U8 8#usize)) (x : I64) :
    ∃ out, integer_encoding.fixed.FixedInt.encode_fixed_vec.default
      (specialize d IntegerFixedDirect.I64.Insts.Integer_encodingFixedFixedIntArrayU88.encode_fixed_light) x = .ok out ∧
      out.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 8 x.bv.toNat := by
  exact generic_total d _ x _ (IntegerFixedProofs.i64_light x)


theorem usize_total (d : integer_encoding.fixed.FixedInt Usize (Array U8 8#usize))
    (x : Usize) (h64 : System.Platform.numBits = 64) :
    ∃ out, integer_encoding.fixed.FixedInt.encode_fixed_vec.default
      (specialize d IntegerFixedDirect.Usize.Insts.Integer_encodingFixedFixedIntArrayU88.encode_fixed_light) x = .ok out ∧
      out.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 8 x.bv.toNat := by
  exact generic_total d _ x _ (IntegerFixedProofs.usize_light x h64)

theorem isize_total (d : integer_encoding.fixed.FixedInt Isize (Array U8 8#usize))
    (x : Isize) (h64 : System.Platform.numBits = 64) :
    ∃ out, integer_encoding.fixed.FixedInt.encode_fixed_vec.default
      (specialize d IntegerFixedDirect.Isize.Insts.Integer_encodingFixedFixedIntArrayU88.encode_fixed_light) x = .ok out ∧
      out.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 8 x.bv.toNat := by
  exact generic_total d _ x _ (IntegerFixedProofs.isize_light x h64)

end IntegerFixedVecProofs
