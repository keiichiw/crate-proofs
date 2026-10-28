import ZigzagDecode
open Aeneas Aeneas.Std Result
namespace integer_encoding

theorem decode_encode_math (z : Int) : zigzagDecode (IntegerEncodingSpec.zigzag z) = z := by
  unfold IntegerEncodingSpec.zigzag zigzagDecode
  split_ifs <;> omega

theorem encode_decode_math (n : Nat) : IntegerEncodingSpec.zigzag (zigzagDecode n) = n := by
  unfold IntegerEncodingSpec.zigzag zigzagDecode
  split_ifs <;> omega

theorem zigzag_decode_encode (x : I64) :
    ∃ encoded, varint.zigzag_encode x = .ok encoded ∧ varint.zigzag_decode encoded = .ok x := by
  obtain ⟨encoded,he,hz⟩ := zigzag_encode_spec x
  obtain ⟨decoded,hd,hv⟩ := zigzag_decode_spec encoded
  have heq : decoded = x := IScalar.eq_of_val_eq
    (hv.trans ((congrArg zigzagDecode hz).trans (decode_encode_math x.val)))
  exact ⟨encoded,he,hd.trans (congrArg Result.ok heq)⟩

theorem zigzag_encode_decode (x : U64) :
    ∃ decoded, varint.zigzag_decode x = .ok decoded ∧ varint.zigzag_encode decoded = .ok x := by
  obtain ⟨decoded,hd,hz⟩ := zigzag_decode_spec x
  obtain ⟨encoded,he,hv⟩ := zigzag_encode_spec decoded
  have heq : encoded = x := UScalar.eq_of_val_eq
    (hv.trans ((congrArg IntegerEncodingSpec.zigzag hz).trans (encode_decode_math x.val)))
  exact ⟨decoded,hd,he.trans (congrArg Result.ok heq)⟩
theorem zigzag_encode_min :
    varint.zigzag_encode (-9223372036854775808)#i64 = .ok 18446744073709551615#u64 := by
  obtain ⟨out,ho,hv⟩ := zigzag_encode_spec (-9223372036854775808)#i64
  have heq : out = 18446744073709551615#u64 := by
    apply UScalar.eq_of_val_eq
    norm_num [IntegerEncodingSpec.zigzag] at hv ⊢
    exact hv
  exact ho.trans (congrArg Result.ok heq)

theorem zigzag_encode_max :
    varint.zigzag_encode (9223372036854775807)#i64 = .ok 18446744073709551614#u64 := by
  obtain ⟨out,ho,hv⟩ := zigzag_encode_spec (9223372036854775807)#i64
  have heq : out = 18446744073709551614#u64 := by
    apply UScalar.eq_of_val_eq
    norm_num [IntegerEncodingSpec.zigzag] at hv ⊢
    exact hv
  exact ho.trans (congrArg Result.ok heq)

theorem zigzag_encode_zero :
    varint.zigzag_encode (0)#i64 = .ok 0#u64 := by
  obtain ⟨out,ho,hv⟩ := zigzag_encode_spec (0)#i64
  have heq : out = 0#u64 := by
    apply UScalar.eq_of_val_eq
    norm_num [IntegerEncodingSpec.zigzag] at hv ⊢
    exact hv
  exact ho.trans (congrArg Result.ok heq)

theorem zigzag_encode_neg_one :
    varint.zigzag_encode (-1)#i64 = .ok 1#u64 := by
  obtain ⟨out,ho,hv⟩ := zigzag_encode_spec (-1)#i64
  have heq : out = 1#u64 := by
    apply UScalar.eq_of_val_eq
    norm_num [IntegerEncodingSpec.zigzag] at hv ⊢
    exact hv
  exact ho.trans (congrArg Result.ok heq)

theorem zigzag_decode_max :
    varint.zigzag_decode 18446744073709551615#u64 = .ok (-9223372036854775808)#i64 := by
  obtain ⟨out,ho,hv⟩ := zigzag_decode_spec 18446744073709551615#u64
  have heq : out = (-9223372036854775808)#i64 := by
    apply IScalar.eq_of_val_eq
    norm_num [zigzagDecode] at hv ⊢
    exact hv
  exact ho.trans (congrArg Result.ok heq)

theorem zigzag_decode_zero :
    varint.zigzag_decode 0#u64 = .ok (0)#i64 := by
  obtain ⟨out,ho,hv⟩ := zigzag_decode_spec 0#u64
  have heq : out = (0)#i64 := by
    apply IScalar.eq_of_val_eq
    norm_num [zigzagDecode] at hv ⊢
    exact hv
  exact ho.trans (congrArg Result.ok heq)

theorem zigzag_decode_one :
    varint.zigzag_decode 1#u64 = .ok (-1)#i64 := by
  obtain ⟨out,ho,hv⟩ := zigzag_decode_spec 1#u64
  have heq : out = (-1)#i64 := by
    apply IScalar.eq_of_val_eq
    norm_num [zigzagDecode] at hv ⊢
    exact hv
  exact ho.trans (congrArg Result.ok heq)

end integer_encoding
