import IntegerVec
import EncodeVar
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace IntegerEncodingVec
open IntegerEncodingSpec IntegerEncodingEncode

def EncodedVec (u : Nat) (out : alloc.vec.Vec U8) : Prop :=
  out.val.length = uLen u ∧
  ∀ j, j < uLen u → out.val[j]!.val =
    (u / 128^j)%128 + if j+1 < uLen u then 128 else 0

theorem generic_total {T : Type} (inst : integer_encoding.varint.VarInt T) (value : T) (u : Nat)
    (hreq : ∃ n, inst.required_space value = .ok n ∧ n.val = uLen u)
    (henc : ∀ dst : Slice U8, uLen u ≤ dst.val.length →
      ∃ out, inst.encode_var value dst = .ok out ∧ Encoded u dst out) :
    ∃ out, integer_encoding.varint.VarInt.encode_var_vec.default inst value = .ok out ∧
      EncodedVec u out := by
  apply integer_encoding.total_result
  unfold integer_encoding.varint.VarInt.encode_var_vec.default
  obtain ⟨n,hn,hlen⟩ := hreq
  rw [hn]
  simp only [bind_ok]
  apply WP.spec_bind (alloc.vec.from_elem_spec core.clone.CloneU8 0#u8 n (by rfl))
  intro vec hvec
  obtain ⟨hv,hl⟩ := hvec
  have hlength : vec.slice.val.length = uLen u := by
    change vec.val.length = _
    rw [hv,List.length_replicate,hlen]
  simp only [alloc.vec.Vec.deref_mut,lift,bind_ok]
  change WP.spec (do
    let encoded ← inst.encode_var value vec.slice
    .ok (⟨encoded.2⟩ : alloc.vec.Vec U8)) (EncodedVec u)
  obtain ⟨encoded,he,hresult⟩ := henc vec.slice (by omega)
  rw [he]
  simp only [bind_ok,WP.spec_ok]
  obtain ⟨hcount,hlenout,hbytes,hsuffix⟩ := hresult
  exact ⟨hlenout.trans hlength,hbytes⟩
/-- Callback dictionary with source-extracted scalar methods. The two unused fields
    remain arbitrary; the actual default body cannot observe their behavior. -/
def sourceDictionary {T : Type} (copy : core.marker.Copy T)
    (required : T → Result Usize)
    (encode : T → Slice U8 → Result (Usize × Slice U8))
    (decode : Slice U8 → Result (Option (T × Usize)))
    (encodeVec : T → Result (alloc.vec.Vec U8)) : integer_encoding.varint.VarInt T where
  coremarkerCopyInst := copy
  required_space := required
  decode_var := decode
  encode_var := encode
  encode_var_vec := encodeVec

theorem u8_total (value : U8)
    (decode : Slice U8 → Result (Option (U8 × Usize)))
    (encodeVec : U8 → Result (alloc.vec.Vec U8)) :
    ∃ out, integer_encoding.varint.VarInt.encode_var_vec.default
      (sourceDictionary core.marker.CopyU8
        integer_encoding.U8.Insts.Integer_encodingVarintVarInt.required_space
        integer_encoding.U8.Insts.Integer_encodingVarintVarInt.encode_var decode encodeVec) value = .ok out ∧
      EncodedVec value.val out := by
  apply generic_total
  · exact IntegerRequiredSpace.u8_required_space value
  · exact fun dst hcap => IntegerEncodingEncode.u8_total value dst hcap

theorem u16_total (value : U16)
    (decode : Slice U8 → Result (Option (U16 × Usize)))
    (encodeVec : U16 → Result (alloc.vec.Vec U8)) :
    ∃ out, integer_encoding.varint.VarInt.encode_var_vec.default
      (sourceDictionary core.marker.CopyU16
        integer_encoding.U16.Insts.Integer_encodingVarintVarInt.required_space
        integer_encoding.U16.Insts.Integer_encodingVarintVarInt.encode_var decode encodeVec) value = .ok out ∧
      EncodedVec value.val out := by
  apply generic_total
  · exact IntegerRequiredSpace.u16_required_space value
  · exact fun dst hcap => IntegerEncodingEncode.u16_total value dst hcap

theorem u32_total (value : U32)
    (decode : Slice U8 → Result (Option (U32 × Usize)))
    (encodeVec : U32 → Result (alloc.vec.Vec U8)) :
    ∃ out, integer_encoding.varint.VarInt.encode_var_vec.default
      (sourceDictionary core.marker.CopyU32
        integer_encoding.U32.Insts.Integer_encodingVarintVarInt.required_space
        integer_encoding.U32.Insts.Integer_encodingVarintVarInt.encode_var decode encodeVec) value = .ok out ∧
      EncodedVec value.val out := by
  apply generic_total
  · exact IntegerRequiredSpace.u32_required_space value
  · exact fun dst hcap => IntegerEncodingEncode.u32_total value dst hcap

theorem u64_total (value : U64)
    (decode : Slice U8 → Result (Option (U64 × Usize)))
    (encodeVec : U64 → Result (alloc.vec.Vec U8)) :
    ∃ out, integer_encoding.varint.VarInt.encode_var_vec.default
      (sourceDictionary core.marker.CopyU64
        integer_encoding.U64.Insts.Integer_encodingVarintVarInt.required_space
        integer_encoding.U64.Insts.Integer_encodingVarintVarInt.encode_var decode encodeVec) value = .ok out ∧
      EncodedVec value.val out := by
  apply generic_total
  · exact IntegerRequiredSpace.u64_required_space value
  · exact fun dst hcap => IntegerEncodingEncode.u64_total value dst hcap

theorem usize_total (value : Usize)
    (decode : Slice U8 → Result (Option (Usize × Usize)))
    (encodeVec : Usize → Result (alloc.vec.Vec U8)) :
    ∃ out, integer_encoding.varint.VarInt.encode_var_vec.default
      (sourceDictionary core.marker.CopyUsize
        integer_encoding.Usize.Insts.Integer_encodingVarintVarInt.required_space
        integer_encoding.Usize.Insts.Integer_encodingVarintVarInt.encode_var decode encodeVec) value = .ok out ∧
      EncodedVec value.val out := by
  apply generic_total
  · exact IntegerRequiredSpace.usize_required_space value
  · exact fun dst hcap => IntegerEncodingEncode.usize_total value dst hcap

theorem i8_total (value : I8)
    (decode : Slice U8 → Result (Option (I8 × Usize)))
    (encodeVec : I8 → Result (alloc.vec.Vec U8)) :
    ∃ out, integer_encoding.varint.VarInt.encode_var_vec.default
      (sourceDictionary core.marker.CopyI8
        integer_encoding.I8.Insts.Integer_encodingVarintVarInt.required_space
        integer_encoding.I8.Insts.Integer_encodingVarintVarInt.encode_var decode encodeVec) value = .ok out ∧
      EncodedVec (zigzag value.val) out := by
  apply generic_total
  · exact IntegerRequiredSpace.i8_required_space value
  · exact fun dst hcap => IntegerEncodingEncode.i8_total value dst hcap

theorem i16_total (value : I16)
    (decode : Slice U8 → Result (Option (I16 × Usize)))
    (encodeVec : I16 → Result (alloc.vec.Vec U8)) :
    ∃ out, integer_encoding.varint.VarInt.encode_var_vec.default
      (sourceDictionary core.marker.CopyI16
        integer_encoding.I16.Insts.Integer_encodingVarintVarInt.required_space
        integer_encoding.I16.Insts.Integer_encodingVarintVarInt.encode_var decode encodeVec) value = .ok out ∧
      EncodedVec (zigzag value.val) out := by
  apply generic_total
  · exact IntegerRequiredSpace.i16_required_space value
  · exact fun dst hcap => IntegerEncodingEncode.i16_total value dst hcap

theorem i32_total (value : I32)
    (decode : Slice U8 → Result (Option (I32 × Usize)))
    (encodeVec : I32 → Result (alloc.vec.Vec U8)) :
    ∃ out, integer_encoding.varint.VarInt.encode_var_vec.default
      (sourceDictionary core.marker.CopyI32
        integer_encoding.I32.Insts.Integer_encodingVarintVarInt.required_space
        integer_encoding.I32.Insts.Integer_encodingVarintVarInt.encode_var decode encodeVec) value = .ok out ∧
      EncodedVec (zigzag value.val) out := by
  apply generic_total
  · exact IntegerRequiredSpace.i32_required_space value
  · exact fun dst hcap => IntegerEncodingEncode.i32_total value dst hcap

theorem i64_total (value : I64)
    (decode : Slice U8 → Result (Option (I64 × Usize)))
    (encodeVec : I64 → Result (alloc.vec.Vec U8)) :
    ∃ out, integer_encoding.varint.VarInt.encode_var_vec.default
      (sourceDictionary core.marker.CopyI64
        integer_encoding.I64.Insts.Integer_encodingVarintVarInt.required_space
        integer_encoding.I64.Insts.Integer_encodingVarintVarInt.encode_var decode encodeVec) value = .ok out ∧
      EncodedVec (zigzag value.val) out := by
  apply generic_total
  · exact IntegerRequiredSpace.i64_required_space value
  · exact fun dst hcap => IntegerEncodingEncode.i64_total value dst hcap

theorem isize_total (value : Isize)
    (decode : Slice U8 → Result (Option (Isize × Usize)))
    (encodeVec : Isize → Result (alloc.vec.Vec U8)) :
    ∃ out, integer_encoding.varint.VarInt.encode_var_vec.default
      (sourceDictionary core.marker.CopyIsize
        integer_encoding.Isize.Insts.Integer_encodingVarintVarInt.required_space
        integer_encoding.Isize.Insts.Integer_encodingVarintVarInt.encode_var decode encodeVec) value = .ok out ∧
      EncodedVec (zigzag value.val) out := by
  apply generic_total
  · exact IntegerRequiredSpace.isize_required_space value
  · exact fun dst hcap => IntegerEncodingEncode.isize_total value dst hcap

end IntegerEncodingVec
