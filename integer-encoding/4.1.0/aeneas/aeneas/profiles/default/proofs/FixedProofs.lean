import IntegerFixedDirect.Funs
import FixedSpec
import RequiredSpace
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace IntegerFixedProofs

theorem u8_light (x : U8) :
    ∃ out, IntegerFixedDirect.U8.Insts.Integer_encodingFixedFixedIntArrayU81.encode_fixed_light x = .ok out ∧
      out.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 1 x.bv.toNat := by
  refine ⟨_, rfl, ?_⟩
  simp only [core.num.U8.to_le_bytes, Array.from_val]
  change (x.bv.toLEBytes.map (fun b => (⟨b⟩ : U8))).map (fun b => b.val) = _
  rw [List.map_map]
  change x.bv.toLEBytes.map (fun b => b.toNat) = _
  exact IntegerEncodingSpec.toLEBytes_arithmetic x.bv

theorem u16_light (x : U16) :
    ∃ out, IntegerFixedDirect.U16.Insts.Integer_encodingFixedFixedIntArrayU82.encode_fixed_light x = .ok out ∧
      out.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 2 x.bv.toNat := by
  refine ⟨_, rfl, ?_⟩
  simp only [core.num.U16.to_le_bytes, Array.from_val]
  change (x.bv.toLEBytes.map (fun b => (⟨b⟩ : U8))).map (fun b => b.val) = _
  rw [List.map_map]
  change x.bv.toLEBytes.map (fun b => b.toNat) = _
  exact IntegerEncodingSpec.toLEBytes_arithmetic x.bv

theorem u32_light (x : U32) :
    ∃ out, IntegerFixedDirect.U32.Insts.Integer_encodingFixedFixedIntArrayU84.encode_fixed_light x = .ok out ∧
      out.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 4 x.bv.toNat := by
  refine ⟨_, rfl, ?_⟩
  simp only [core.num.U32.to_le_bytes, Array.from_val]
  change (x.bv.toLEBytes.map (fun b => (⟨b⟩ : U8))).map (fun b => b.val) = _
  rw [List.map_map]
  change x.bv.toLEBytes.map (fun b => b.toNat) = _
  exact IntegerEncodingSpec.toLEBytes_arithmetic x.bv

theorem u64_light (x : U64) :
    ∃ out, IntegerFixedDirect.U64.Insts.Integer_encodingFixedFixedIntArrayU88.encode_fixed_light x = .ok out ∧
      out.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 8 x.bv.toNat := by
  refine ⟨_, rfl, ?_⟩
  simp only [core.num.U64.to_le_bytes, Array.from_val]
  change (x.bv.toLEBytes.map (fun b => (⟨b⟩ : U8))).map (fun b => b.val) = _
  rw [List.map_map]
  change x.bv.toLEBytes.map (fun b => b.toNat) = _
  exact IntegerEncodingSpec.toLEBytes_arithmetic x.bv

theorem i8_light (x : I8) :
    ∃ out, IntegerFixedDirect.I8.Insts.Integer_encodingFixedFixedIntArrayU81.encode_fixed_light x = .ok out ∧
      out.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 1 x.bv.toNat := by
  refine ⟨_, rfl, ?_⟩
  simp only [core.num.I8.to_le_bytes, Array.from_val]
  change (x.bv.toLEBytes.map (fun b => (⟨b⟩ : U8))).map (fun b => b.val) = _
  rw [List.map_map]
  change x.bv.toLEBytes.map (fun b => b.toNat) = _
  exact IntegerEncodingSpec.toLEBytes_arithmetic x.bv

theorem i16_light (x : I16) :
    ∃ out, IntegerFixedDirect.I16.Insts.Integer_encodingFixedFixedIntArrayU82.encode_fixed_light x = .ok out ∧
      out.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 2 x.bv.toNat := by
  refine ⟨_, rfl, ?_⟩
  simp only [core.num.I16.to_le_bytes, Array.from_val]
  change (x.bv.toLEBytes.map (fun b => (⟨b⟩ : U8))).map (fun b => b.val) = _
  rw [List.map_map]
  change x.bv.toLEBytes.map (fun b => b.toNat) = _
  exact IntegerEncodingSpec.toLEBytes_arithmetic x.bv

theorem i32_light (x : I32) :
    ∃ out, IntegerFixedDirect.I32.Insts.Integer_encodingFixedFixedIntArrayU84.encode_fixed_light x = .ok out ∧
      out.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 4 x.bv.toNat := by
  refine ⟨_, rfl, ?_⟩
  simp only [core.num.I32.to_le_bytes, Array.from_val]
  change (x.bv.toLEBytes.map (fun b => (⟨b⟩ : U8))).map (fun b => b.val) = _
  rw [List.map_map]
  change x.bv.toLEBytes.map (fun b => b.toNat) = _
  exact IntegerEncodingSpec.toLEBytes_arithmetic x.bv

theorem i64_light (x : I64) :
    ∃ out, IntegerFixedDirect.I64.Insts.Integer_encodingFixedFixedIntArrayU88.encode_fixed_light x = .ok out ∧
      out.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 8 x.bv.toNat := by
  refine ⟨_, rfl, ?_⟩
  simp only [core.num.I64.to_le_bytes, Array.from_val]
  change (x.bv.toLEBytes.map (fun b => (⟨b⟩ : U8))).map (fun b => b.val) = _
  rw [List.map_map]
  change x.bv.toLEBytes.map (fun b => b.toNat) = _
  exact IntegerEncodingSpec.toLEBytes_arithmetic x.bv


theorem uscalar_card (ty : UScalarTy) : Nat.card (UScalar ty) = 2^ty.numBits := by
  let e : UScalar ty ≃ BitVec ty.numBits := ⟨UScalar.bv, UScalar.mk, by intro x; cases x; rfl, by intro x; rfl⟩
  rw [Nat.card_congr e, Nat.card_congr ((BitVec.equivFin (m := ty.numBits)).toEquiv)]
  exact Nat.card_fin _

theorem iscalar_card (ty : IScalarTy) : Nat.card (IScalar ty) = 2^ty.numBits := by
  let e : IScalar ty ≃ BitVec ty.numBits := ⟨IScalar.bv, IScalar.mk, by intro x; cases x; rfl, by intro x; rfl⟩
  rw [Nat.card_congr e, Nat.card_congr ((BitVec.equivFin (m := ty.numBits)).toEquiv)]
  exact Nat.card_fin _

theorem size_u8 : IntegerFixedDirect.core.mem.size_of U8 = .ok 1#usize := by
  simp [IntegerFixedDirect.core.mem.size_of, uscalar_card]

theorem u8_encode (x : U8) (dst : Slice U8) :
    ∃ out, IntegerFixedDirect.U8.Insts.Integer_encodingFixedFixedIntArrayU81.encode_fixed x dst = .ok out ∧
      (if dst.val.length = 1 then out.1 = some () ∧
        out.2.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 1 x.bv.toNat
       else out = (none, dst)) := by
  unfold IntegerFixedDirect.U8.Insts.Integer_encodingFixedFixedIntArrayU81.encode_fixed
  rw [size_u8]
  simp only [bind_ok]
  by_cases h : dst.len = 1#usize
  · simp only [h, ↓reduceIte]
    obtain ⟨a, ha, hab⟩ := u8_light x
    have hab' : (core.num.U8.to_le_bytes x).val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 1 x.bv.toNat := by
      have he : a = core.num.U8.to_le_bytes x := by simpa [IntegerFixedDirect.U8.Insts.Integer_encodingFixedFixedIntArrayU81.encode_fixed_light] using ha.symm
      simpa [he] using hab
    simp only [lift, bind_ok]
    have hl : dst.val.length = 1 := by scalar_tac
    simp only [IntegerFixedDirect.core.slice.Slice.clone_from_slice, Array.val_to_slice]
    have ht : dst.val.length = (core.num.U8.to_le_bytes x).val.length := by rw [Array.property]; exact hl
    simp only [ht, and_self, ↓reduceIte, bind_ok]
    refine ⟨(some (), (core.num.U8.to_le_bytes x).to_slice), rfl, ?_⟩
    simpa [hl, Array.val_to_slice, Array.property] using hab'
  · have hl : dst.val.length ≠ 1 := by intro he; apply h; scalar_tac
    simp only [h, hl, ↓reduceIte]
    exact ⟨(none,dst), rfl, rfl⟩

theorem size_u16 : IntegerFixedDirect.core.mem.size_of U16 = .ok 2#usize := by
  simp [IntegerFixedDirect.core.mem.size_of, uscalar_card]

theorem u16_encode (x : U16) (dst : Slice U8) :
    ∃ out, IntegerFixedDirect.U16.Insts.Integer_encodingFixedFixedIntArrayU82.encode_fixed x dst = .ok out ∧
      (if dst.val.length = 2 then out.1 = some () ∧
        out.2.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 2 x.bv.toNat
       else out = (none, dst)) := by
  unfold IntegerFixedDirect.U16.Insts.Integer_encodingFixedFixedIntArrayU82.encode_fixed
  rw [size_u16]
  simp only [bind_ok]
  by_cases h : dst.len = 2#usize
  · simp only [h, ↓reduceIte]
    obtain ⟨a, ha, hab⟩ := u16_light x
    have hab' : (core.num.U16.to_le_bytes x).val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 2 x.bv.toNat := by
      have he : a = core.num.U16.to_le_bytes x := by simpa [IntegerFixedDirect.U16.Insts.Integer_encodingFixedFixedIntArrayU82.encode_fixed_light] using ha.symm
      simpa [he] using hab
    simp only [lift, bind_ok]
    have hl : dst.val.length = 2 := by scalar_tac
    simp only [IntegerFixedDirect.core.slice.Slice.clone_from_slice, Array.val_to_slice]
    have ht : dst.val.length = (core.num.U16.to_le_bytes x).val.length := by rw [Array.property]; exact hl
    simp only [ht, and_self, ↓reduceIte, bind_ok]
    refine ⟨(some (), (core.num.U16.to_le_bytes x).to_slice), rfl, ?_⟩
    simpa [hl, Array.val_to_slice, Array.property] using hab'
  · have hl : dst.val.length ≠ 2 := by intro he; apply h; scalar_tac
    simp only [h, hl, ↓reduceIte]
    exact ⟨(none,dst), rfl, rfl⟩

theorem size_u32 : IntegerFixedDirect.core.mem.size_of U32 = .ok 4#usize := by
  simp [IntegerFixedDirect.core.mem.size_of, uscalar_card]

theorem u32_encode (x : U32) (dst : Slice U8) :
    ∃ out, IntegerFixedDirect.U32.Insts.Integer_encodingFixedFixedIntArrayU84.encode_fixed x dst = .ok out ∧
      (if dst.val.length = 4 then out.1 = some () ∧
        out.2.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 4 x.bv.toNat
       else out = (none, dst)) := by
  unfold IntegerFixedDirect.U32.Insts.Integer_encodingFixedFixedIntArrayU84.encode_fixed
  rw [size_u32]
  simp only [bind_ok]
  by_cases h : dst.len = 4#usize
  · simp only [h, ↓reduceIte]
    obtain ⟨a, ha, hab⟩ := u32_light x
    have hab' : (core.num.U32.to_le_bytes x).val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 4 x.bv.toNat := by
      have he : a = core.num.U32.to_le_bytes x := by simpa [IntegerFixedDirect.U32.Insts.Integer_encodingFixedFixedIntArrayU84.encode_fixed_light] using ha.symm
      simpa [he] using hab
    simp only [lift, bind_ok]
    have hl : dst.val.length = 4 := by scalar_tac
    simp only [IntegerFixedDirect.core.slice.Slice.clone_from_slice, Array.val_to_slice]
    have ht : dst.val.length = (core.num.U32.to_le_bytes x).val.length := by rw [Array.property]; exact hl
    simp only [ht, and_self, ↓reduceIte, bind_ok]
    refine ⟨(some (), (core.num.U32.to_le_bytes x).to_slice), rfl, ?_⟩
    simpa [hl, Array.val_to_slice, Array.property] using hab'
  · have hl : dst.val.length ≠ 4 := by intro he; apply h; scalar_tac
    simp only [h, hl, ↓reduceIte]
    exact ⟨(none,dst), rfl, rfl⟩

theorem size_u64 : IntegerFixedDirect.core.mem.size_of U64 = .ok 8#usize := by
  simp [IntegerFixedDirect.core.mem.size_of, uscalar_card]

theorem u64_encode (x : U64) (dst : Slice U8) :
    ∃ out, IntegerFixedDirect.U64.Insts.Integer_encodingFixedFixedIntArrayU88.encode_fixed x dst = .ok out ∧
      (if dst.val.length = 8 then out.1 = some () ∧
        out.2.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 8 x.bv.toNat
       else out = (none, dst)) := by
  unfold IntegerFixedDirect.U64.Insts.Integer_encodingFixedFixedIntArrayU88.encode_fixed
  rw [size_u64]
  simp only [bind_ok]
  by_cases h : dst.len = 8#usize
  · simp only [h, ↓reduceIte]
    obtain ⟨a, ha, hab⟩ := u64_light x
    have hab' : (core.num.U64.to_le_bytes x).val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 8 x.bv.toNat := by
      have he : a = core.num.U64.to_le_bytes x := by simpa [IntegerFixedDirect.U64.Insts.Integer_encodingFixedFixedIntArrayU88.encode_fixed_light] using ha.symm
      simpa [he] using hab
    simp only [lift, bind_ok]
    have hl : dst.val.length = 8 := by scalar_tac
    simp only [IntegerFixedDirect.core.slice.Slice.clone_from_slice, Array.val_to_slice]
    have ht : dst.val.length = (core.num.U64.to_le_bytes x).val.length := by rw [Array.property]; exact hl
    simp only [ht, and_self, ↓reduceIte, bind_ok]
    refine ⟨(some (), (core.num.U64.to_le_bytes x).to_slice), rfl, ?_⟩
    simpa [hl, Array.val_to_slice, Array.property] using hab'
  · have hl : dst.val.length ≠ 8 := by intro he; apply h; scalar_tac
    simp only [h, hl, ↓reduceIte]
    exact ⟨(none,dst), rfl, rfl⟩

theorem size_i8 : IntegerFixedDirect.core.mem.size_of I8 = .ok 1#usize := by
  simp [IntegerFixedDirect.core.mem.size_of, iscalar_card]

theorem i8_encode (x : I8) (dst : Slice U8) :
    ∃ out, IntegerFixedDirect.I8.Insts.Integer_encodingFixedFixedIntArrayU81.encode_fixed x dst = .ok out ∧
      (if dst.val.length = 1 then out.1 = some () ∧
        out.2.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 1 x.bv.toNat
       else out = (none, dst)) := by
  unfold IntegerFixedDirect.I8.Insts.Integer_encodingFixedFixedIntArrayU81.encode_fixed
  rw [size_i8]
  simp only [bind_ok]
  by_cases h : dst.len = 1#usize
  · simp only [h, ↓reduceIte]
    obtain ⟨a, ha, hab⟩ := i8_light x
    have hab' : (core.num.I8.to_le_bytes x).val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 1 x.bv.toNat := by
      have he : a = core.num.I8.to_le_bytes x := by simpa [IntegerFixedDirect.I8.Insts.Integer_encodingFixedFixedIntArrayU81.encode_fixed_light] using ha.symm
      simpa [he] using hab
    simp only [lift, bind_ok]
    have hl : dst.val.length = 1 := by scalar_tac
    simp only [IntegerFixedDirect.core.slice.Slice.clone_from_slice, Array.val_to_slice]
    have ht : dst.val.length = (core.num.I8.to_le_bytes x).val.length := by rw [Array.property]; exact hl
    simp only [ht, and_self, ↓reduceIte, bind_ok]
    refine ⟨(some (), (core.num.I8.to_le_bytes x).to_slice), rfl, ?_⟩
    simpa [hl, Array.val_to_slice, Array.property] using hab'
  · have hl : dst.val.length ≠ 1 := by intro he; apply h; scalar_tac
    simp only [h, hl, ↓reduceIte]
    exact ⟨(none,dst), rfl, rfl⟩

theorem size_i16 : IntegerFixedDirect.core.mem.size_of I16 = .ok 2#usize := by
  simp [IntegerFixedDirect.core.mem.size_of, iscalar_card]

theorem i16_encode (x : I16) (dst : Slice U8) :
    ∃ out, IntegerFixedDirect.I16.Insts.Integer_encodingFixedFixedIntArrayU82.encode_fixed x dst = .ok out ∧
      (if dst.val.length = 2 then out.1 = some () ∧
        out.2.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 2 x.bv.toNat
       else out = (none, dst)) := by
  unfold IntegerFixedDirect.I16.Insts.Integer_encodingFixedFixedIntArrayU82.encode_fixed
  rw [size_i16]
  simp only [bind_ok]
  by_cases h : dst.len = 2#usize
  · simp only [h, ↓reduceIte]
    obtain ⟨a, ha, hab⟩ := i16_light x
    have hab' : (core.num.I16.to_le_bytes x).val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 2 x.bv.toNat := by
      have he : a = core.num.I16.to_le_bytes x := by simpa [IntegerFixedDirect.I16.Insts.Integer_encodingFixedFixedIntArrayU82.encode_fixed_light] using ha.symm
      simpa [he] using hab
    simp only [lift, bind_ok]
    have hl : dst.val.length = 2 := by scalar_tac
    simp only [IntegerFixedDirect.core.slice.Slice.clone_from_slice, Array.val_to_slice]
    have ht : dst.val.length = (core.num.I16.to_le_bytes x).val.length := by rw [Array.property]; exact hl
    simp only [ht, and_self, ↓reduceIte, bind_ok]
    refine ⟨(some (), (core.num.I16.to_le_bytes x).to_slice), rfl, ?_⟩
    simpa [hl, Array.val_to_slice, Array.property] using hab'
  · have hl : dst.val.length ≠ 2 := by intro he; apply h; scalar_tac
    simp only [h, hl, ↓reduceIte]
    exact ⟨(none,dst), rfl, rfl⟩

theorem size_i32 : IntegerFixedDirect.core.mem.size_of I32 = .ok 4#usize := by
  simp [IntegerFixedDirect.core.mem.size_of, iscalar_card]

theorem i32_encode (x : I32) (dst : Slice U8) :
    ∃ out, IntegerFixedDirect.I32.Insts.Integer_encodingFixedFixedIntArrayU84.encode_fixed x dst = .ok out ∧
      (if dst.val.length = 4 then out.1 = some () ∧
        out.2.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 4 x.bv.toNat
       else out = (none, dst)) := by
  unfold IntegerFixedDirect.I32.Insts.Integer_encodingFixedFixedIntArrayU84.encode_fixed
  rw [size_i32]
  simp only [bind_ok]
  by_cases h : dst.len = 4#usize
  · simp only [h, ↓reduceIte]
    obtain ⟨a, ha, hab⟩ := i32_light x
    have hab' : (core.num.I32.to_le_bytes x).val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 4 x.bv.toNat := by
      have he : a = core.num.I32.to_le_bytes x := by simpa [IntegerFixedDirect.I32.Insts.Integer_encodingFixedFixedIntArrayU84.encode_fixed_light] using ha.symm
      simpa [he] using hab
    simp only [lift, bind_ok]
    have hl : dst.val.length = 4 := by scalar_tac
    simp only [IntegerFixedDirect.core.slice.Slice.clone_from_slice, Array.val_to_slice]
    have ht : dst.val.length = (core.num.I32.to_le_bytes x).val.length := by rw [Array.property]; exact hl
    simp only [ht, and_self, ↓reduceIte, bind_ok]
    refine ⟨(some (), (core.num.I32.to_le_bytes x).to_slice), rfl, ?_⟩
    simpa [hl, Array.val_to_slice, Array.property] using hab'
  · have hl : dst.val.length ≠ 4 := by intro he; apply h; scalar_tac
    simp only [h, hl, ↓reduceIte]
    exact ⟨(none,dst), rfl, rfl⟩

theorem size_i64 : IntegerFixedDirect.core.mem.size_of I64 = .ok 8#usize := by
  simp [IntegerFixedDirect.core.mem.size_of, iscalar_card]

theorem i64_encode (x : I64) (dst : Slice U8) :
    ∃ out, IntegerFixedDirect.I64.Insts.Integer_encodingFixedFixedIntArrayU88.encode_fixed x dst = .ok out ∧
      (if dst.val.length = 8 then out.1 = some () ∧
        out.2.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 8 x.bv.toNat
       else out = (none, dst)) := by
  unfold IntegerFixedDirect.I64.Insts.Integer_encodingFixedFixedIntArrayU88.encode_fixed
  rw [size_i64]
  simp only [bind_ok]
  by_cases h : dst.len = 8#usize
  · simp only [h, ↓reduceIte]
    obtain ⟨a, ha, hab⟩ := i64_light x
    have hab' : (core.num.I64.to_le_bytes x).val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 8 x.bv.toNat := by
      have he : a = core.num.I64.to_le_bytes x := by simpa [IntegerFixedDirect.I64.Insts.Integer_encodingFixedFixedIntArrayU88.encode_fixed_light] using ha.symm
      simpa [he] using hab
    simp only [lift, bind_ok]
    have hl : dst.val.length = 8 := by scalar_tac
    simp only [IntegerFixedDirect.core.slice.Slice.clone_from_slice, Array.val_to_slice]
    have ht : dst.val.length = (core.num.I64.to_le_bytes x).val.length := by rw [Array.property]; exact hl
    simp only [ht, and_self, ↓reduceIte, bind_ok]
    refine ⟨(some (), (core.num.I64.to_le_bytes x).to_slice), rfl, ?_⟩
    simpa [hl, Array.val_to_slice, Array.property] using hab'
  · have hl : dst.val.length ≠ 8 := by intro he; apply h; scalar_tac
    simp only [h, hl, ↓reduceIte]
    exact ⟨(none,dst), rfl, rfl⟩



theorem from_u8 (a : Array U8 1#usize) :
    (core.num.U8.from_le_bytes a).bv.toNat = IntegerEncodingSpec.fixedValue (a.val.map (fun b => b.val)) := by
  change ((BitVec.fromLEBytes (a.val.map U8.bv)).cast (by simp [Array.property])).toNat = _
  rw [BitVec.toNat_cast, IntegerEncodingSpec.fromLEBytes_arithmetic, List.map_map]
  rfl

theorem u8_decode (src : Slice U8) :
    ∃ out, IntegerFixedDirect.U8.Insts.Integer_encodingFixedFixedIntArrayU81.decode_fixed src = .ok out ∧
      (if src.val.length = 1 then ∃ v, out = some v ∧
        v.bv.toNat = IntegerEncodingSpec.fixedValue (src.val.map (fun b => b.val))
       else out = none) := by
  unfold IntegerFixedDirect.U8.Insts.Integer_encodingFixedFixedIntArrayU81.decode_fixed
  rw [size_u8]
  simp only [bind_ok]
  by_cases h : src.len = 1#usize
  · simp only [h, ↓reduceIte]
    have hl : src.val.length = 1 := by scalar_tac
    have hlen : src.length = 1#usize := by scalar_tac
    simp only [core.array.TryFromArrayCopySlice.try_from, hlen, ↓reduceDIte, bind_ok,
      IntegerFixedDirect.core.result.Result.unwrap, lift, bind_ok]
    refine ⟨some _, rfl, ?_⟩
    refine ⟨_, rfl, ?_⟩
    rw [from_u8]
    simp only [Array.from_val]
  · have hl : src.val.length ≠ 1 := by intro he; apply h; scalar_tac
    simp only [h, hl, ↓reduceIte]
    exact ⟨none, rfl, rfl⟩

theorem u8_switch (x : U8) :
    ∃ out, IntegerFixedDirect.U8.Insts.Integer_encodingFixedFixedIntArrayU81.switch_endianness x = .ok out ∧
      out.bv.toNat = IntegerEncodingSpec.fixedValue
        ((IntegerEncodingSpec.fixedBytes 1 x.bv.toNat).reverse) := by
  unfold IntegerFixedDirect.U8.Insts.Integer_encodingFixedFixedIntArrayU81.switch_endianness
  simp only [lift, bind_ok]
  refine ⟨_, rfl, ?_⟩
  rw [from_u8]
  simp only [core.num.U8.to_be_bytes, Array.from_val, List.map_map]
  change IntegerEncodingSpec.fixedValue (x.bv.toBEBytes.map (fun b => b.toNat)) = _
  simp only [BitVec.toBEBytes, List.map_reverse]
  rw [IntegerEncodingSpec.toLEBytes_arithmetic]

theorem from_u16 (a : Array U8 2#usize) :
    (core.num.U16.from_le_bytes a).bv.toNat = IntegerEncodingSpec.fixedValue (a.val.map (fun b => b.val)) := by
  change ((BitVec.fromLEBytes (a.val.map U8.bv)).cast (by simp [Array.property])).toNat = _
  rw [BitVec.toNat_cast, IntegerEncodingSpec.fromLEBytes_arithmetic, List.map_map]
  rfl

theorem u16_decode (src : Slice U8) :
    ∃ out, IntegerFixedDirect.U16.Insts.Integer_encodingFixedFixedIntArrayU82.decode_fixed src = .ok out ∧
      (if src.val.length = 2 then ∃ v, out = some v ∧
        v.bv.toNat = IntegerEncodingSpec.fixedValue (src.val.map (fun b => b.val))
       else out = none) := by
  unfold IntegerFixedDirect.U16.Insts.Integer_encodingFixedFixedIntArrayU82.decode_fixed
  rw [size_u16]
  simp only [bind_ok]
  by_cases h : src.len = 2#usize
  · simp only [h, ↓reduceIte]
    have hl : src.val.length = 2 := by scalar_tac
    have hlen : src.length = 2#usize := by scalar_tac
    simp only [core.array.TryFromArrayCopySlice.try_from, hlen, ↓reduceDIte, bind_ok,
      IntegerFixedDirect.core.result.Result.unwrap, lift, bind_ok]
    refine ⟨some _, rfl, ?_⟩
    refine ⟨_, rfl, ?_⟩
    rw [from_u16]
    simp only [Array.from_val]
  · have hl : src.val.length ≠ 2 := by intro he; apply h; scalar_tac
    simp only [h, hl, ↓reduceIte]
    exact ⟨none, rfl, rfl⟩

theorem u16_switch (x : U16) :
    ∃ out, IntegerFixedDirect.U16.Insts.Integer_encodingFixedFixedIntArrayU82.switch_endianness x = .ok out ∧
      out.bv.toNat = IntegerEncodingSpec.fixedValue
        ((IntegerEncodingSpec.fixedBytes 2 x.bv.toNat).reverse) := by
  unfold IntegerFixedDirect.U16.Insts.Integer_encodingFixedFixedIntArrayU82.switch_endianness
  simp only [lift, bind_ok]
  refine ⟨_, rfl, ?_⟩
  rw [from_u16]
  simp only [core.num.U16.to_be_bytes, Array.from_val, List.map_map]
  change IntegerEncodingSpec.fixedValue (x.bv.toBEBytes.map (fun b => b.toNat)) = _
  simp only [BitVec.toBEBytes, List.map_reverse]
  rw [IntegerEncodingSpec.toLEBytes_arithmetic]

theorem from_u32 (a : Array U8 4#usize) :
    (core.num.U32.from_le_bytes a).bv.toNat = IntegerEncodingSpec.fixedValue (a.val.map (fun b => b.val)) := by
  change ((BitVec.fromLEBytes (a.val.map U8.bv)).cast (by simp [Array.property])).toNat = _
  rw [BitVec.toNat_cast, IntegerEncodingSpec.fromLEBytes_arithmetic, List.map_map]
  rfl

theorem u32_decode (src : Slice U8) :
    ∃ out, IntegerFixedDirect.U32.Insts.Integer_encodingFixedFixedIntArrayU84.decode_fixed src = .ok out ∧
      (if src.val.length = 4 then ∃ v, out = some v ∧
        v.bv.toNat = IntegerEncodingSpec.fixedValue (src.val.map (fun b => b.val))
       else out = none) := by
  unfold IntegerFixedDirect.U32.Insts.Integer_encodingFixedFixedIntArrayU84.decode_fixed
  rw [size_u32]
  simp only [bind_ok]
  by_cases h : src.len = 4#usize
  · simp only [h, ↓reduceIte]
    have hl : src.val.length = 4 := by scalar_tac
    have hlen : src.length = 4#usize := by scalar_tac
    simp only [core.array.TryFromArrayCopySlice.try_from, hlen, ↓reduceDIte, bind_ok,
      IntegerFixedDirect.core.result.Result.unwrap, lift, bind_ok]
    refine ⟨some _, rfl, ?_⟩
    refine ⟨_, rfl, ?_⟩
    rw [from_u32]
    simp only [Array.from_val]
  · have hl : src.val.length ≠ 4 := by intro he; apply h; scalar_tac
    simp only [h, hl, ↓reduceIte]
    exact ⟨none, rfl, rfl⟩

theorem u32_switch (x : U32) :
    ∃ out, IntegerFixedDirect.U32.Insts.Integer_encodingFixedFixedIntArrayU84.switch_endianness x = .ok out ∧
      out.bv.toNat = IntegerEncodingSpec.fixedValue
        ((IntegerEncodingSpec.fixedBytes 4 x.bv.toNat).reverse) := by
  unfold IntegerFixedDirect.U32.Insts.Integer_encodingFixedFixedIntArrayU84.switch_endianness
  simp only [lift, bind_ok]
  refine ⟨_, rfl, ?_⟩
  rw [from_u32]
  simp only [core.num.U32.to_be_bytes, Array.from_val, List.map_map]
  change IntegerEncodingSpec.fixedValue (x.bv.toBEBytes.map (fun b => b.toNat)) = _
  simp only [BitVec.toBEBytes, List.map_reverse]
  rw [IntegerEncodingSpec.toLEBytes_arithmetic]

theorem from_u64 (a : Array U8 8#usize) :
    (core.num.U64.from_le_bytes a).bv.toNat = IntegerEncodingSpec.fixedValue (a.val.map (fun b => b.val)) := by
  change ((BitVec.fromLEBytes (a.val.map U8.bv)).cast (by simp [Array.property])).toNat = _
  rw [BitVec.toNat_cast, IntegerEncodingSpec.fromLEBytes_arithmetic, List.map_map]
  rfl

theorem u64_decode (src : Slice U8) :
    ∃ out, IntegerFixedDirect.U64.Insts.Integer_encodingFixedFixedIntArrayU88.decode_fixed src = .ok out ∧
      (if src.val.length = 8 then ∃ v, out = some v ∧
        v.bv.toNat = IntegerEncodingSpec.fixedValue (src.val.map (fun b => b.val))
       else out = none) := by
  unfold IntegerFixedDirect.U64.Insts.Integer_encodingFixedFixedIntArrayU88.decode_fixed
  rw [size_u64]
  simp only [bind_ok]
  by_cases h : src.len = 8#usize
  · simp only [h, ↓reduceIte]
    have hl : src.val.length = 8 := by scalar_tac
    have hlen : src.length = 8#usize := by scalar_tac
    simp only [core.array.TryFromArrayCopySlice.try_from, hlen, ↓reduceDIte, bind_ok,
      IntegerFixedDirect.core.result.Result.unwrap, lift, bind_ok]
    refine ⟨some _, rfl, ?_⟩
    refine ⟨_, rfl, ?_⟩
    rw [from_u64]
    simp only [Array.from_val]
  · have hl : src.val.length ≠ 8 := by intro he; apply h; scalar_tac
    simp only [h, hl, ↓reduceIte]
    exact ⟨none, rfl, rfl⟩

theorem u64_switch (x : U64) :
    ∃ out, IntegerFixedDirect.U64.Insts.Integer_encodingFixedFixedIntArrayU88.switch_endianness x = .ok out ∧
      out.bv.toNat = IntegerEncodingSpec.fixedValue
        ((IntegerEncodingSpec.fixedBytes 8 x.bv.toNat).reverse) := by
  unfold IntegerFixedDirect.U64.Insts.Integer_encodingFixedFixedIntArrayU88.switch_endianness
  simp only [lift, bind_ok]
  refine ⟨_, rfl, ?_⟩
  rw [from_u64]
  simp only [core.num.U64.to_be_bytes, Array.from_val, List.map_map]
  change IntegerEncodingSpec.fixedValue (x.bv.toBEBytes.map (fun b => b.toNat)) = _
  simp only [BitVec.toBEBytes, List.map_reverse]
  rw [IntegerEncodingSpec.toLEBytes_arithmetic]

theorem from_i8 (a : Array U8 1#usize) :
    (core.num.I8.from_le_bytes a).bv.toNat = IntegerEncodingSpec.fixedValue (a.val.map (fun b => b.val)) := by
  change ((BitVec.fromLEBytes (a.val.map U8.bv)).cast (by simp [Array.property])).toNat = _
  rw [BitVec.toNat_cast, IntegerEncodingSpec.fromLEBytes_arithmetic, List.map_map]
  rfl

theorem i8_decode (src : Slice U8) :
    ∃ out, IntegerFixedDirect.I8.Insts.Integer_encodingFixedFixedIntArrayU81.decode_fixed src = .ok out ∧
      (if src.val.length = 1 then ∃ v, out = some v ∧
        v.bv.toNat = IntegerEncodingSpec.fixedValue (src.val.map (fun b => b.val))
       else out = none) := by
  unfold IntegerFixedDirect.I8.Insts.Integer_encodingFixedFixedIntArrayU81.decode_fixed
  rw [size_i8]
  simp only [bind_ok]
  by_cases h : src.len = 1#usize
  · simp only [h, ↓reduceIte]
    have hl : src.val.length = 1 := by scalar_tac
    have hlen : src.length = 1#usize := by scalar_tac
    simp only [core.array.TryFromArrayCopySlice.try_from, hlen, ↓reduceDIte, bind_ok,
      IntegerFixedDirect.core.result.Result.unwrap, lift, bind_ok]
    refine ⟨some _, rfl, ?_⟩
    refine ⟨_, rfl, ?_⟩
    rw [from_i8]
    simp only [Array.from_val]
  · have hl : src.val.length ≠ 1 := by intro he; apply h; scalar_tac
    simp only [h, hl, ↓reduceIte]
    exact ⟨none, rfl, rfl⟩

theorem i8_switch (x : I8) :
    ∃ out, IntegerFixedDirect.I8.Insts.Integer_encodingFixedFixedIntArrayU81.switch_endianness x = .ok out ∧
      out.bv.toNat = IntegerEncodingSpec.fixedValue
        ((IntegerEncodingSpec.fixedBytes 1 x.bv.toNat).reverse) := by
  unfold IntegerFixedDirect.I8.Insts.Integer_encodingFixedFixedIntArrayU81.switch_endianness
  simp only [lift, bind_ok]
  refine ⟨_, rfl, ?_⟩
  rw [from_i8]
  simp only [core.num.I8.to_be_bytes, Array.from_val, List.map_map]
  change IntegerEncodingSpec.fixedValue (x.bv.toBEBytes.map (fun b => b.toNat)) = _
  simp only [BitVec.toBEBytes, List.map_reverse]
  rw [IntegerEncodingSpec.toLEBytes_arithmetic]

theorem from_i16 (a : Array U8 2#usize) :
    (core.num.I16.from_le_bytes a).bv.toNat = IntegerEncodingSpec.fixedValue (a.val.map (fun b => b.val)) := by
  change ((BitVec.fromLEBytes (a.val.map U8.bv)).cast (by simp [Array.property])).toNat = _
  rw [BitVec.toNat_cast, IntegerEncodingSpec.fromLEBytes_arithmetic, List.map_map]
  rfl

theorem i16_decode (src : Slice U8) :
    ∃ out, IntegerFixedDirect.I16.Insts.Integer_encodingFixedFixedIntArrayU82.decode_fixed src = .ok out ∧
      (if src.val.length = 2 then ∃ v, out = some v ∧
        v.bv.toNat = IntegerEncodingSpec.fixedValue (src.val.map (fun b => b.val))
       else out = none) := by
  unfold IntegerFixedDirect.I16.Insts.Integer_encodingFixedFixedIntArrayU82.decode_fixed
  rw [size_i16]
  simp only [bind_ok]
  by_cases h : src.len = 2#usize
  · simp only [h, ↓reduceIte]
    have hl : src.val.length = 2 := by scalar_tac
    have hlen : src.length = 2#usize := by scalar_tac
    simp only [core.array.TryFromArrayCopySlice.try_from, hlen, ↓reduceDIte, bind_ok,
      IntegerFixedDirect.core.result.Result.unwrap, lift, bind_ok]
    refine ⟨some _, rfl, ?_⟩
    refine ⟨_, rfl, ?_⟩
    rw [from_i16]
    simp only [Array.from_val]
  · have hl : src.val.length ≠ 2 := by intro he; apply h; scalar_tac
    simp only [h, hl, ↓reduceIte]
    exact ⟨none, rfl, rfl⟩

theorem i16_switch (x : I16) :
    ∃ out, IntegerFixedDirect.I16.Insts.Integer_encodingFixedFixedIntArrayU82.switch_endianness x = .ok out ∧
      out.bv.toNat = IntegerEncodingSpec.fixedValue
        ((IntegerEncodingSpec.fixedBytes 2 x.bv.toNat).reverse) := by
  unfold IntegerFixedDirect.I16.Insts.Integer_encodingFixedFixedIntArrayU82.switch_endianness
  simp only [lift, bind_ok]
  refine ⟨_, rfl, ?_⟩
  rw [from_i16]
  simp only [core.num.I16.to_be_bytes, Array.from_val, List.map_map]
  change IntegerEncodingSpec.fixedValue (x.bv.toBEBytes.map (fun b => b.toNat)) = _
  simp only [BitVec.toBEBytes, List.map_reverse]
  rw [IntegerEncodingSpec.toLEBytes_arithmetic]

theorem from_i32 (a : Array U8 4#usize) :
    (core.num.I32.from_le_bytes a).bv.toNat = IntegerEncodingSpec.fixedValue (a.val.map (fun b => b.val)) := by
  change ((BitVec.fromLEBytes (a.val.map U8.bv)).cast (by simp [Array.property])).toNat = _
  rw [BitVec.toNat_cast, IntegerEncodingSpec.fromLEBytes_arithmetic, List.map_map]
  rfl

theorem i32_decode (src : Slice U8) :
    ∃ out, IntegerFixedDirect.I32.Insts.Integer_encodingFixedFixedIntArrayU84.decode_fixed src = .ok out ∧
      (if src.val.length = 4 then ∃ v, out = some v ∧
        v.bv.toNat = IntegerEncodingSpec.fixedValue (src.val.map (fun b => b.val))
       else out = none) := by
  unfold IntegerFixedDirect.I32.Insts.Integer_encodingFixedFixedIntArrayU84.decode_fixed
  rw [size_i32]
  simp only [bind_ok]
  by_cases h : src.len = 4#usize
  · simp only [h, ↓reduceIte]
    have hl : src.val.length = 4 := by scalar_tac
    have hlen : src.length = 4#usize := by scalar_tac
    simp only [core.array.TryFromArrayCopySlice.try_from, hlen, ↓reduceDIte, bind_ok,
      IntegerFixedDirect.core.result.Result.unwrap, lift, bind_ok]
    refine ⟨some _, rfl, ?_⟩
    refine ⟨_, rfl, ?_⟩
    rw [from_i32]
    simp only [Array.from_val]
  · have hl : src.val.length ≠ 4 := by intro he; apply h; scalar_tac
    simp only [h, hl, ↓reduceIte]
    exact ⟨none, rfl, rfl⟩

theorem i32_switch (x : I32) :
    ∃ out, IntegerFixedDirect.I32.Insts.Integer_encodingFixedFixedIntArrayU84.switch_endianness x = .ok out ∧
      out.bv.toNat = IntegerEncodingSpec.fixedValue
        ((IntegerEncodingSpec.fixedBytes 4 x.bv.toNat).reverse) := by
  unfold IntegerFixedDirect.I32.Insts.Integer_encodingFixedFixedIntArrayU84.switch_endianness
  simp only [lift, bind_ok]
  refine ⟨_, rfl, ?_⟩
  rw [from_i32]
  simp only [core.num.I32.to_be_bytes, Array.from_val, List.map_map]
  change IntegerEncodingSpec.fixedValue (x.bv.toBEBytes.map (fun b => b.toNat)) = _
  simp only [BitVec.toBEBytes, List.map_reverse]
  rw [IntegerEncodingSpec.toLEBytes_arithmetic]

theorem from_i64 (a : Array U8 8#usize) :
    (core.num.I64.from_le_bytes a).bv.toNat = IntegerEncodingSpec.fixedValue (a.val.map (fun b => b.val)) := by
  change ((BitVec.fromLEBytes (a.val.map U8.bv)).cast (by simp [Array.property])).toNat = _
  rw [BitVec.toNat_cast, IntegerEncodingSpec.fromLEBytes_arithmetic, List.map_map]
  rfl

theorem i64_decode (src : Slice U8) :
    ∃ out, IntegerFixedDirect.I64.Insts.Integer_encodingFixedFixedIntArrayU88.decode_fixed src = .ok out ∧
      (if src.val.length = 8 then ∃ v, out = some v ∧
        v.bv.toNat = IntegerEncodingSpec.fixedValue (src.val.map (fun b => b.val))
       else out = none) := by
  unfold IntegerFixedDirect.I64.Insts.Integer_encodingFixedFixedIntArrayU88.decode_fixed
  rw [size_i64]
  simp only [bind_ok]
  by_cases h : src.len = 8#usize
  · simp only [h, ↓reduceIte]
    have hl : src.val.length = 8 := by scalar_tac
    have hlen : src.length = 8#usize := by scalar_tac
    simp only [core.array.TryFromArrayCopySlice.try_from, hlen, ↓reduceDIte, bind_ok,
      IntegerFixedDirect.core.result.Result.unwrap, lift, bind_ok]
    refine ⟨some _, rfl, ?_⟩
    refine ⟨_, rfl, ?_⟩
    rw [from_i64]
    simp only [Array.from_val]
  · have hl : src.val.length ≠ 8 := by intro he; apply h; scalar_tac
    simp only [h, hl, ↓reduceIte]
    exact ⟨none, rfl, rfl⟩

theorem i64_switch (x : I64) :
    ∃ out, IntegerFixedDirect.I64.Insts.Integer_encodingFixedFixedIntArrayU88.switch_endianness x = .ok out ∧
      out.bv.toNat = IntegerEncodingSpec.fixedValue
        ((IntegerEncodingSpec.fixedBytes 8 x.bv.toNat).reverse) := by
  unfold IntegerFixedDirect.I64.Insts.Integer_encodingFixedFixedIntArrayU88.switch_endianness
  simp only [lift, bind_ok]
  refine ⟨_, rfl, ?_⟩
  rw [from_i64]
  simp only [core.num.I64.to_be_bytes, Array.from_val, List.map_map]
  change IntegerEncodingSpec.fixedValue (x.bv.toBEBytes.map (fun b => b.toNat)) = _
  simp only [BitVec.toBEBytes, List.map_reverse]
  rw [IntegerEncodingSpec.toLEBytes_arithmetic]


theorem usize_light (x : Usize) (h64 : System.Platform.numBits = 64) :
    ∃ out, IntegerFixedDirect.Usize.Insts.Integer_encodingFixedFixedIntArrayU88.encode_fixed_light x = .ok out ∧
      out.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 8 x.bv.toNat := by
  refine ⟨_, rfl, ?_⟩
  simp only [IntegerFixedDirect.core.num.Usize.to_le_bytes, core.num.U64.to_le_bytes, Array.from_val, List.map_map]
  change (x.bv.setWidth 64).toLEBytes.map (fun b => b.toNat) = _
  rw [IntegerEncodingSpec.toLEBytes_arithmetic]
  have hx : x.bv.toNat < 2^64 := by simpa only [UScalarTy.Usize_numBits_eq, h64] using x.bv.isLt
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]

theorem size_usize (h64 : System.Platform.numBits = 64) : IntegerFixedDirect.core.mem.size_of Usize = .ok 8#usize := by
  simp [IntegerFixedDirect.core.mem.size_of, uscalar_card, h64]

theorem from_usize (a : Array U8 8#usize) (h64 : System.Platform.numBits = 64) :
    (IntegerFixedDirect.core.num.Usize.from_le_bytes a).bv.toNat = IntegerEncodingSpec.fixedValue (a.val.map (fun b => b.val)) := by
  change ((core.num.U64.from_le_bytes a).bv.setWidth _).toNat = _
  rw [BitVec.toNat_setWidth]
  have hx : (core.num.U64.from_le_bytes a).bv.toNat < 2^System.Platform.numBits := by simpa only [h64] using (core.num.U64.from_le_bytes a).bv.isLt
  rw [Nat.mod_eq_of_lt hx]
  exact from_u64 a

theorem usize_encode (x : Usize) (dst : Slice U8) (h64 : System.Platform.numBits = 64) :
    ∃ out, IntegerFixedDirect.Usize.Insts.Integer_encodingFixedFixedIntArrayU88.encode_fixed x dst = .ok out ∧
      (if dst.val.length = 8 then out.1 = some () ∧
        out.2.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 8 x.bv.toNat
       else out = (none, dst)) := by
  unfold IntegerFixedDirect.Usize.Insts.Integer_encodingFixedFixedIntArrayU88.encode_fixed
  rw [size_usize h64]
  simp only [bind_ok]
  by_cases h : dst.len = 8#usize
  · simp only [h, ↓reduceIte]
    obtain ⟨a, ha, hab⟩ := usize_light x h64
    have hab' : (IntegerFixedDirect.core.num.Usize.to_le_bytes x).val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 8 x.bv.toNat := by
      have he : a = IntegerFixedDirect.core.num.Usize.to_le_bytes x := by simpa [IntegerFixedDirect.Usize.Insts.Integer_encodingFixedFixedIntArrayU88.encode_fixed_light] using ha.symm
      simpa [he] using hab
    simp only [lift, bind_ok]
    have hl : dst.val.length = 8 := by scalar_tac
    simp only [IntegerFixedDirect.core.slice.Slice.clone_from_slice, Array.val_to_slice]
    have ht : dst.val.length = (IntegerFixedDirect.core.num.Usize.to_le_bytes x).val.length := by rw [Array.property]; exact hl
    simp only [ht, and_self, ↓reduceIte, bind_ok]
    refine ⟨(some (), (IntegerFixedDirect.core.num.Usize.to_le_bytes x).to_slice), rfl, ?_⟩
    simpa [hl, Array.val_to_slice, Array.property] using hab'
  · have hl : dst.val.length ≠ 8 := by intro he; apply h; scalar_tac
    simp only [h, hl, ↓reduceIte]
    exact ⟨(none,dst), rfl, rfl⟩

theorem usize_decode (src : Slice U8) (h64 : System.Platform.numBits = 64) :
    ∃ out, IntegerFixedDirect.Usize.Insts.Integer_encodingFixedFixedIntArrayU88.decode_fixed src = .ok out ∧
      (if src.val.length = 8 then ∃ v, out = some v ∧
        v.bv.toNat = IntegerEncodingSpec.fixedValue (src.val.map (fun b => b.val))
       else out = none) := by
  unfold IntegerFixedDirect.Usize.Insts.Integer_encodingFixedFixedIntArrayU88.decode_fixed
  rw [size_usize h64]
  simp only [bind_ok]
  by_cases h : src.len = 8#usize
  · simp only [h, ↓reduceIte]
    have hl : src.val.length = 8 := by scalar_tac
    have hlen : src.length = 8#usize := by scalar_tac
    simp only [core.array.TryFromArrayCopySlice.try_from, hlen, ↓reduceDIte, bind_ok,
      IntegerFixedDirect.core.result.Result.unwrap, lift, bind_ok]
    refine ⟨some _, rfl, ?_⟩
    refine ⟨_, rfl, ?_⟩
    rw [from_usize _ h64]
    simp only [Array.from_val]
  · have hl : src.val.length ≠ 8 := by intro he; apply h; scalar_tac
    simp only [h, hl, ↓reduceIte]
    exact ⟨none, rfl, rfl⟩

theorem usize_switch (x : Usize) (h64 : System.Platform.numBits = 64) :
    ∃ out, IntegerFixedDirect.Usize.Insts.Integer_encodingFixedFixedIntArrayU88.switch_endianness x = .ok out ∧
      out.bv.toNat = IntegerEncodingSpec.fixedValue
        ((IntegerEncodingSpec.fixedBytes 8 x.bv.toNat).reverse) := by
  unfold IntegerFixedDirect.Usize.Insts.Integer_encodingFixedFixedIntArrayU88.switch_endianness
  simp only [lift, bind_ok]
  refine ⟨_, rfl, ?_⟩
  rw [from_usize _ h64]
  simp only [IntegerFixedDirect.core.num.Usize.to_be_bytes, core.num.U64.to_be_bytes, Array.from_val, List.map_map]
  change IntegerEncodingSpec.fixedValue ((x.bv.setWidth 64).toBEBytes.map (fun b => b.toNat)) = _
  simp only [BitVec.toBEBytes, List.map_reverse]
  rw [IntegerEncodingSpec.toLEBytes_arithmetic]
  have hx : x.bv.toNat < 2^64 := by simpa only [UScalarTy.Usize_numBits_eq, h64] using x.bv.isLt
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]

theorem isize_light (x : Isize) (h64 : System.Platform.numBits = 64) :
    ∃ out, IntegerFixedDirect.Isize.Insts.Integer_encodingFixedFixedIntArrayU88.encode_fixed_light x = .ok out ∧
      out.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 8 x.bv.toNat := by
  refine ⟨_, rfl, ?_⟩
  simp only [IntegerFixedDirect.core.num.Isize.to_le_bytes, core.num.I64.to_le_bytes, Array.from_val, List.map_map]
  change (x.bv.setWidth 64).toLEBytes.map (fun b => b.toNat) = _
  rw [IntegerEncodingSpec.toLEBytes_arithmetic]
  have hx : x.bv.toNat < 2^64 := by simpa only [IScalarTy.Isize_numBits_eq, h64] using x.bv.isLt
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]

theorem size_isize (h64 : System.Platform.numBits = 64) : IntegerFixedDirect.core.mem.size_of Isize = .ok 8#usize := by
  simp [IntegerFixedDirect.core.mem.size_of, iscalar_card, h64]

theorem from_isize (a : Array U8 8#usize) (h64 : System.Platform.numBits = 64) :
    (IntegerFixedDirect.core.num.Isize.from_le_bytes a).bv.toNat = IntegerEncodingSpec.fixedValue (a.val.map (fun b => b.val)) := by
  change ((core.num.I64.from_le_bytes a).bv.setWidth _).toNat = _
  rw [BitVec.toNat_setWidth]
  have hx : (core.num.I64.from_le_bytes a).bv.toNat < 2^System.Platform.numBits := by simpa only [h64] using (core.num.I64.from_le_bytes a).bv.isLt
  rw [Nat.mod_eq_of_lt hx]
  exact from_i64 a

theorem isize_encode (x : Isize) (dst : Slice U8) (h64 : System.Platform.numBits = 64) :
    ∃ out, IntegerFixedDirect.Isize.Insts.Integer_encodingFixedFixedIntArrayU88.encode_fixed x dst = .ok out ∧
      (if dst.val.length = 8 then out.1 = some () ∧
        out.2.val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 8 x.bv.toNat
       else out = (none, dst)) := by
  unfold IntegerFixedDirect.Isize.Insts.Integer_encodingFixedFixedIntArrayU88.encode_fixed
  rw [size_isize h64]
  simp only [bind_ok]
  by_cases h : dst.len = 8#usize
  · simp only [h, ↓reduceIte]
    obtain ⟨a, ha, hab⟩ := isize_light x h64
    have hab' : (IntegerFixedDirect.core.num.Isize.to_le_bytes x).val.map (fun b => b.val) = IntegerEncodingSpec.fixedBytes 8 x.bv.toNat := by
      have he : a = IntegerFixedDirect.core.num.Isize.to_le_bytes x := by simpa [IntegerFixedDirect.Isize.Insts.Integer_encodingFixedFixedIntArrayU88.encode_fixed_light] using ha.symm
      simpa [he] using hab
    simp only [lift, bind_ok]
    have hl : dst.val.length = 8 := by scalar_tac
    simp only [IntegerFixedDirect.core.slice.Slice.clone_from_slice, Array.val_to_slice]
    have ht : dst.val.length = (IntegerFixedDirect.core.num.Isize.to_le_bytes x).val.length := by rw [Array.property]; exact hl
    simp only [ht, and_self, ↓reduceIte, bind_ok]
    refine ⟨(some (), (IntegerFixedDirect.core.num.Isize.to_le_bytes x).to_slice), rfl, ?_⟩
    simpa [hl, Array.val_to_slice, Array.property] using hab'
  · have hl : dst.val.length ≠ 8 := by intro he; apply h; scalar_tac
    simp only [h, hl, ↓reduceIte]
    exact ⟨(none,dst), rfl, rfl⟩



theorem isize_decode (src : Slice U8) (h64 : System.Platform.numBits = 64) :
    ∃ out, IntegerFixedDirect.Isize.Insts.Integer_encodingFixedFixedIntArrayU88.decode_fixed src = .ok out ∧
      (if src.val.length = 8 then ∃ v, out = some v ∧
        v.bv.toNat = IntegerEncodingSpec.fixedValue (src.val.map (fun b => b.val))
       else out = none) := by
  unfold IntegerFixedDirect.Isize.Insts.Integer_encodingFixedFixedIntArrayU88.decode_fixed
  rw [size_isize h64]
  simp only [bind_ok]
  by_cases h : src.len = 8#usize
  · simp only [h, ↓reduceIte]
    have hl : src.val.length = 8 := by scalar_tac
    have hlen : src.length = 8#usize := by scalar_tac
    simp only [core.array.TryFromArrayCopySlice.try_from, hlen, ↓reduceDIte, bind_ok,
      IntegerFixedDirect.core.result.Result.unwrap, lift, bind_ok]
    refine ⟨some _, rfl, ?_⟩
    refine ⟨_, rfl, ?_⟩
    rw [from_isize _ h64]
    simp only [Array.from_val]
  · have hl : src.val.length ≠ 8 := by intro he; apply h; scalar_tac
    simp only [h, hl, ↓reduceIte]
    exact ⟨none, rfl, rfl⟩

theorem isize_switch (x : Isize) (h64 : System.Platform.numBits = 64) :
    ∃ out, IntegerFixedDirect.Isize.Insts.Integer_encodingFixedFixedIntArrayU88.switch_endianness x = .ok out ∧
      out.bv.toNat = IntegerEncodingSpec.fixedValue
        ((IntegerEncodingSpec.fixedBytes 8 x.bv.toNat).reverse) := by
  unfold IntegerFixedDirect.Isize.Insts.Integer_encodingFixedFixedIntArrayU88.switch_endianness
  simp only [lift, bind_ok]
  refine ⟨_, rfl, ?_⟩
  rw [from_isize _ h64]
  simp only [IntegerFixedDirect.core.num.Isize.to_be_bytes, core.num.I64.to_be_bytes, Array.from_val, List.map_map]
  change IntegerEncodingSpec.fixedValue ((x.bv.setWidth 64).toBEBytes.map (fun b => b.toNat)) = _
  simp only [BitVec.toBEBytes, List.map_reverse]
  rw [IntegerEncodingSpec.toLEBytes_arithmetic]
  have hx : x.bv.toNat < 2^64 := by simpa only [IScalarTy.Isize_numBits_eq, h64] using x.bv.isLt
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]


theorem i8_decode_signed (src : Slice U8) :
    ∃ out, IntegerFixedDirect.I8.Insts.Integer_encodingFixedFixedIntArrayU81.decode_fixed src = .ok out ∧
      (if src.val.length = 1 then ∃ v, out = some v ∧
        v.val = IntegerEncodingSpec.signedValue 8
          (IntegerEncodingSpec.fixedValue (src.val.map (fun b => b.val)))
       else out = none) := by
  obtain ⟨out, ho, hv⟩ := i8_decode src
  refine ⟨out, ho, ?_⟩
  by_cases h : src.val.length = 1
  · simp only [h, ↓reduceIte] at hv ⊢
    obtain ⟨v, hvo, hvb⟩ := hv
    refine ⟨v, hvo, ?_⟩
    change v.bv.toInt = _
    rw [IntegerEncodingSpec.toInt_arithmetic, hvb]
  · simpa only [h, ↓reduceIte] using hv

theorem i8_switch_signed (x : I8) :
    ∃ out, IntegerFixedDirect.I8.Insts.Integer_encodingFixedFixedIntArrayU81.switch_endianness x = .ok out ∧
      out.val = IntegerEncodingSpec.signedValue 8 (IntegerEncodingSpec.fixedValue
        ((IntegerEncodingSpec.fixedBytes 1 x.bv.toNat).reverse)) := by
  obtain ⟨out, ho, hv⟩ := i8_switch x
  refine ⟨out, ho, ?_⟩
  change out.bv.toInt = _
  rw [IntegerEncodingSpec.toInt_arithmetic, hv]

theorem i16_decode_signed (src : Slice U8) :
    ∃ out, IntegerFixedDirect.I16.Insts.Integer_encodingFixedFixedIntArrayU82.decode_fixed src = .ok out ∧
      (if src.val.length = 2 then ∃ v, out = some v ∧
        v.val = IntegerEncodingSpec.signedValue 16
          (IntegerEncodingSpec.fixedValue (src.val.map (fun b => b.val)))
       else out = none) := by
  obtain ⟨out, ho, hv⟩ := i16_decode src
  refine ⟨out, ho, ?_⟩
  by_cases h : src.val.length = 2
  · simp only [h, ↓reduceIte] at hv ⊢
    obtain ⟨v, hvo, hvb⟩ := hv
    refine ⟨v, hvo, ?_⟩
    change v.bv.toInt = _
    rw [IntegerEncodingSpec.toInt_arithmetic, hvb]
  · simpa only [h, ↓reduceIte] using hv

theorem i16_switch_signed (x : I16) :
    ∃ out, IntegerFixedDirect.I16.Insts.Integer_encodingFixedFixedIntArrayU82.switch_endianness x = .ok out ∧
      out.val = IntegerEncodingSpec.signedValue 16 (IntegerEncodingSpec.fixedValue
        ((IntegerEncodingSpec.fixedBytes 2 x.bv.toNat).reverse)) := by
  obtain ⟨out, ho, hv⟩ := i16_switch x
  refine ⟨out, ho, ?_⟩
  change out.bv.toInt = _
  rw [IntegerEncodingSpec.toInt_arithmetic, hv]

theorem i32_decode_signed (src : Slice U8) :
    ∃ out, IntegerFixedDirect.I32.Insts.Integer_encodingFixedFixedIntArrayU84.decode_fixed src = .ok out ∧
      (if src.val.length = 4 then ∃ v, out = some v ∧
        v.val = IntegerEncodingSpec.signedValue 32
          (IntegerEncodingSpec.fixedValue (src.val.map (fun b => b.val)))
       else out = none) := by
  obtain ⟨out, ho, hv⟩ := i32_decode src
  refine ⟨out, ho, ?_⟩
  by_cases h : src.val.length = 4
  · simp only [h, ↓reduceIte] at hv ⊢
    obtain ⟨v, hvo, hvb⟩ := hv
    refine ⟨v, hvo, ?_⟩
    change v.bv.toInt = _
    rw [IntegerEncodingSpec.toInt_arithmetic, hvb]
  · simpa only [h, ↓reduceIte] using hv

theorem i32_switch_signed (x : I32) :
    ∃ out, IntegerFixedDirect.I32.Insts.Integer_encodingFixedFixedIntArrayU84.switch_endianness x = .ok out ∧
      out.val = IntegerEncodingSpec.signedValue 32 (IntegerEncodingSpec.fixedValue
        ((IntegerEncodingSpec.fixedBytes 4 x.bv.toNat).reverse)) := by
  obtain ⟨out, ho, hv⟩ := i32_switch x
  refine ⟨out, ho, ?_⟩
  change out.bv.toInt = _
  rw [IntegerEncodingSpec.toInt_arithmetic, hv]

theorem i64_decode_signed (src : Slice U8) :
    ∃ out, IntegerFixedDirect.I64.Insts.Integer_encodingFixedFixedIntArrayU88.decode_fixed src = .ok out ∧
      (if src.val.length = 8 then ∃ v, out = some v ∧
        v.val = IntegerEncodingSpec.signedValue 64
          (IntegerEncodingSpec.fixedValue (src.val.map (fun b => b.val)))
       else out = none) := by
  obtain ⟨out, ho, hv⟩ := i64_decode src
  refine ⟨out, ho, ?_⟩
  by_cases h : src.val.length = 8
  · simp only [h, ↓reduceIte] at hv ⊢
    obtain ⟨v, hvo, hvb⟩ := hv
    refine ⟨v, hvo, ?_⟩
    change v.bv.toInt = _
    rw [IntegerEncodingSpec.toInt_arithmetic, hvb]
  · simpa only [h, ↓reduceIte] using hv

theorem i64_switch_signed (x : I64) :
    ∃ out, IntegerFixedDirect.I64.Insts.Integer_encodingFixedFixedIntArrayU88.switch_endianness x = .ok out ∧
      out.val = IntegerEncodingSpec.signedValue 64 (IntegerEncodingSpec.fixedValue
        ((IntegerEncodingSpec.fixedBytes 8 x.bv.toNat).reverse)) := by
  obtain ⟨out, ho, hv⟩ := i64_switch x
  refine ⟨out, ho, ?_⟩
  change out.bv.toInt = _
  rw [IntegerEncodingSpec.toInt_arithmetic, hv]

theorem isize_decode_signed (src : Slice U8) (h64 : System.Platform.numBits = 64) :
    ∃ out, IntegerFixedDirect.Isize.Insts.Integer_encodingFixedFixedIntArrayU88.decode_fixed src = .ok out ∧
      (if src.val.length = 8 then ∃ v, out = some v ∧
        v.val = IntegerEncodingSpec.signedValue 64
          (IntegerEncodingSpec.fixedValue (src.val.map (fun b => b.val)))
       else out = none) := by
  obtain ⟨out, ho, hv⟩ := isize_decode src h64
  refine ⟨out, ho, ?_⟩
  by_cases h : src.val.length = 8
  · simp only [h, ↓reduceIte] at hv ⊢
    obtain ⟨v, hvo, hvb⟩ := hv
    refine ⟨v, hvo, ?_⟩
    change v.bv.toInt = _
    rw [IntegerEncodingSpec.toInt_arithmetic, hvb]
    simp only [IScalarTy.Isize_numBits_eq, h64]
  · simpa only [h, ↓reduceIte] using hv

theorem isize_switch_signed (x : Isize) (h64 : System.Platform.numBits = 64) :
    ∃ out, IntegerFixedDirect.Isize.Insts.Integer_encodingFixedFixedIntArrayU88.switch_endianness x = .ok out ∧
      out.val = IntegerEncodingSpec.signedValue 64 (IntegerEncodingSpec.fixedValue
        ((IntegerEncodingSpec.fixedBytes 8 x.bv.toNat).reverse)) := by
  obtain ⟨out, ho, hv⟩ := isize_switch x h64
  refine ⟨out, ho, ?_⟩
  change out.bv.toInt = _
  rw [IntegerEncodingSpec.toInt_arithmetic, hv]
  simp only [IScalarTy.Isize_numBits_eq, h64]
end IntegerFixedProofs
