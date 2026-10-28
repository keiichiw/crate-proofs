import EncodeVar
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace IntegerEncodingEncodeErrors
open IntegerEncodingSpec

/-- This is the extracted debug-assertion profile; Rust release builds can disable it. -/
theorem u64_too_small (v : U64) (dst : Slice U8) (hsmall : dst.val.length < uLen v.val) :
    integer_encoding.U64.Insts.Integer_encodingVarintVarInt.encode_var v dst =
      .fail .assertionFailure := by
  obtain ⟨space,hs,hval⟩ := IntegerRequiredSpace.u64_required_space v
  unfold integer_encoding.U64.Insts.Integer_encodingVarintVarInt.encode_var
  rw [hs]
  have hn : ¬space.val ≤ dst.val.length := by omega
  simp [hn]

theorem i64_too_small (v : I64) (dst : Slice U8) (hsmall : dst.val.length < uLen (zigzag v.val)) :
    integer_encoding.I64.Insts.Integer_encodingVarintVarInt.encode_var v dst =
      .fail .assertionFailure := by
  obtain ⟨space,hs,hval⟩ := IntegerRequiredSpace.i64_required_space v
  unfold integer_encoding.I64.Insts.Integer_encodingVarintVarInt.encode_var
  rw [hs]
  have hn : ¬space.val ≤ dst.val.length := by omega
  simp [hn]

theorem u8_too_small (v : U8) (dst : Slice U8) (hsmall : dst.val.length < uLen v.val) :
    integer_encoding.U8.Insts.Integer_encodingVarintVarInt.encode_var v dst =
      .fail .assertionFailure := by
  unfold integer_encoding.U8.Insts.Integer_encodingVarintVarInt.encode_var
  simp only [lift,bind_ok]
  have hc := u64_too_small (UScalar.cast .U64 v) dst
  apply hc
  simpa using hsmall

theorem u16_too_small (v : U16) (dst : Slice U8) (hsmall : dst.val.length < uLen v.val) :
    integer_encoding.U16.Insts.Integer_encodingVarintVarInt.encode_var v dst =
      .fail .assertionFailure := by
  unfold integer_encoding.U16.Insts.Integer_encodingVarintVarInt.encode_var
  simp only [lift,bind_ok]
  have hc := u64_too_small (UScalar.cast .U64 v) dst
  apply hc
  simpa using hsmall

theorem u32_too_small (v : U32) (dst : Slice U8) (hsmall : dst.val.length < uLen v.val) :
    integer_encoding.U32.Insts.Integer_encodingVarintVarInt.encode_var v dst =
      .fail .assertionFailure := by
  unfold integer_encoding.U32.Insts.Integer_encodingVarintVarInt.encode_var
  simp only [lift,bind_ok]
  have hc := u64_too_small (UScalar.cast .U64 v) dst
  apply hc
  simpa using hsmall

theorem usize_too_small (v : Usize) (dst : Slice U8) (hsmall : dst.val.length < uLen v.val) :
    integer_encoding.Usize.Insts.Integer_encodingVarintVarInt.encode_var v dst =
      .fail .assertionFailure := by
  unfold integer_encoding.Usize.Insts.Integer_encodingVarintVarInt.encode_var
  simp only [lift,bind_ok]
  have hc := u64_too_small (UScalar.cast .U64 v) dst
  apply hc
  simpa using hsmall

theorem i8_too_small (v : I8) (dst : Slice U8) (hsmall : dst.val.length < uLen (zigzag v.val)) :
    integer_encoding.I8.Insts.Integer_encodingVarintVarInt.encode_var v dst =
      .fail .assertionFailure := by
  unfold integer_encoding.I8.Insts.Integer_encodingVarintVarInt.encode_var
  simp only [lift,bind_ok]
  have hc := i64_too_small (IScalar.cast .I64 v) dst
  apply hc
  simpa using hsmall

theorem i16_too_small (v : I16) (dst : Slice U8) (hsmall : dst.val.length < uLen (zigzag v.val)) :
    integer_encoding.I16.Insts.Integer_encodingVarintVarInt.encode_var v dst =
      .fail .assertionFailure := by
  unfold integer_encoding.I16.Insts.Integer_encodingVarintVarInt.encode_var
  simp only [lift,bind_ok]
  have hc := i64_too_small (IScalar.cast .I64 v) dst
  apply hc
  simpa using hsmall

theorem i32_too_small (v : I32) (dst : Slice U8) (hsmall : dst.val.length < uLen (zigzag v.val)) :
    integer_encoding.I32.Insts.Integer_encodingVarintVarInt.encode_var v dst =
      .fail .assertionFailure := by
  unfold integer_encoding.I32.Insts.Integer_encodingVarintVarInt.encode_var
  simp only [lift,bind_ok]
  have hc := i64_too_small (IScalar.cast .I64 v) dst
  apply hc
  simpa using hsmall

theorem isize_too_small (v : Isize) (dst : Slice U8) (hsmall : dst.val.length < uLen (zigzag v.val)) :
    integer_encoding.Isize.Insts.Integer_encodingVarintVarInt.encode_var v dst =
      .fail .assertionFailure := by
  unfold integer_encoding.Isize.Insts.Integer_encodingVarintVarInt.encode_var
  simp only [lift,bind_ok]
  have hc := i64_too_small (IScalar.cast .I64 v) dst
  apply hc
  simpa using hsmall

end IntegerEncodingEncodeErrors
