module
public import Proofs.AddressConversions
public import Proofs.OrderMath

public section

/-! Independent network-order value of an IPv6 address assembled from eight
16-bit segments. The selected constructor model must separately be connected
to these bytes; this file does not assert a Rust constructor contract. -/
namespace IPv6ConstructorMath

open Aeneas Aeneas.Std

@[expose] def segmentBytes : List U16 → List U8
  | [] => []
  | x :: xs => (core.num.U16.to_be_bytes x).val ++ segmentBytes xs

@[expose] def segmentValue (xs : List U16) : Nat :=
  OrderMath.digitsValue 65536 (xs.map UScalar.val)

theorem u16_to_be_bytes_value (x : U16) :
    CidrModel.bytesValue (core.num.U16.to_be_bytes x).val = x.val := by
  have h := AddressConversions.fromBEValue
    (x.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8))
  have hmap :
      ((x.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8)).map U8.bv) =
        x.bv.toBEBytes := by
    simp [List.map_map, Function.comp_def]
  rw [hmap, AddressConversions.be_roundtrip 16 (by decide)] at h
  simpa only [core.num.U16.to_be_bytes, Array.from_val, U16.bv_toNat] using h.symm

theorem bytesValue_append (xs ys : List U8) :
    CidrModel.bytesValue (xs ++ ys) =
      CidrModel.bytesValue xs * 256 ^ ys.length + CidrModel.bytesValue ys := by
  induction xs with
  | nil => simp [CidrModel.bytesValue]
  | cons x xs ih =>
    simp only [List.cons_append, CidrModel.bytesValue,
      List.length_append]
    rw [ih]
    rw [show xs.length + ys.length = ys.length + xs.length by omega]
    rw [pow_add]
    ring

theorem segmentBytes_length (xs : List U16) :
    (segmentBytes xs).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : (core.num.U16.to_be_bytes x).val.length = 2 :=
      Array.property _
    simp [segmentBytes, hx, ih]
    omega

theorem segmentBytes_value (xs : List U16) :
    CidrModel.bytesValue (segmentBytes xs) = segmentValue xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hpow : 256 ^ (2 * xs.length) = 65536 ^ xs.length := by
      rw [pow_mul]
      norm_num
    simp only [segmentBytes, segmentValue, List.map_cons,
      OrderMath.digitsValue, List.length_map]
    rw [bytesValue_append, segmentBytes_length, u16_to_be_bytes_value, ih,
      hpow]
    rfl

theorem eight_segments_bytes_length (xs : List U16) (h : xs.length = 8) :
    (segmentBytes xs).length = 16 := by
  rw [segmentBytes_length, h]

theorem eight_segments_value_bound (xs : List U16) (h : xs.length = 8) :
    segmentValue xs < 2 ^ 128 := by
  rw [← segmentBytes_value]
  have hb := CidrModel.bytesValue_bound (segmentBytes xs)
  rw [eight_segments_bytes_length xs h] at hb
  simpa using hb

/-- The registered eight-segment constructor has the independent big-endian value. -/
theorem ipv6_new_value_spec (a b c d e f g h : U16) :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv6Addr.new a b c d e f g h = Result.ok out ∧
      CidrModel.ipv6Value out = segmentValue [a,b,c,d,e,f,g,h] := by
  let out : ipnet.core.net.ip_addr.Ipv6Addr :=
    { octets := Array.from (segmentBytes [a,b,c,d,e,f,g,h])
        (by simp [segmentBytes_length]) }
  refine ⟨out, ?_, ?_⟩
  · simp [ipnet.core.net.ip_addr.Ipv6Addr.new, out, segmentBytes]
  · simpa only [out, CidrModel.ipv6Value, Array.from_val] using
      (segmentBytes_value [a,b,c,d,e,f,g,h])

theorem ipv6_new_zero_spec :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv6Addr.new
        0#u16 0#u16 0#u16 0#u16 0#u16 0#u16 0#u16 0#u16 =
        Result.ok out ∧ CidrModel.ipv6Value out = 0 := by
  rcases ipv6_new_value_spec
      0#u16 0#u16 0#u16 0#u16 0#u16 0#u16 0#u16 0#u16 with
    ⟨out, hnew, hvalue⟩
  refine ⟨out, hnew, ?_⟩
  simpa [segmentValue, OrderMath.digitsValue] using hvalue

theorem ipv6_new_one_spec :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv6Addr.new
        0#u16 0#u16 0#u16 0#u16 0#u16 0#u16 0#u16 1#u16 =
        Result.ok out ∧ CidrModel.ipv6Value out = 1 := by
  rcases ipv6_new_value_spec
      0#u16 0#u16 0#u16 0#u16 0#u16 0#u16 0#u16 1#u16 with
    ⟨out, hnew, hvalue⟩
  refine ⟨out, hnew, ?_⟩
  simpa [segmentValue, OrderMath.digitsValue] using hvalue

theorem ipv6_new_max_spec :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv6Addr.new
        65535#u16 65535#u16 65535#u16 65535#u16
        65535#u16 65535#u16 65535#u16 65535#u16 =
        Result.ok out ∧ CidrModel.ipv6Value out = 2 ^ 128 - 1 := by
  rcases ipv6_new_value_spec
      65535#u16 65535#u16 65535#u16 65535#u16
      65535#u16 65535#u16 65535#u16 65535#u16 with
    ⟨out, hnew, hvalue⟩
  refine ⟨out, hnew, ?_⟩
  simpa [segmentValue, OrderMath.digitsValue] using hvalue

end IPv6ConstructorMath
