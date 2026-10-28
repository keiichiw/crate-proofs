module
public import Proofs.CidrModel

public section

namespace AddressConversions

open Aeneas Aeneas.Std CidrModel

def leValue : List U8 → Nat
| [] => 0
| b::bs => b.val + 256 * leValue bs

theorem fromLEValue (bs : List U8) :
    (BitVec.fromLEBytes (bs.map U8.bv)).toNat = leValue bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb := U8.lt_succ_max b
    have ht : (BitVec.fromLEBytes (bs.map U8.bv)).toNat < 2 ^ (8 * bs.length) := by
      simpa using (BitVec.isLt (BitVec.fromLEBytes (bs.map U8.bv)))
    have hlarge : b.val < 2 ^ (8 * (bs.length + 1)) := by
      have hp : 256 ≤ 2 ^ (8 * (bs.length + 1)) := by
        simp [Nat.mul_add, pow_add]
      omega
    rw [List.map_cons, BitVec.fromLEBytes.eq_2]
    simp only [BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
      U8.bv_toNat, List.length_cons, List.length_map, leValue]
    have hpow : 2 ^ (8 * (bs.length + 1)) = 2 ^ (8 * bs.length) * 256 := by
      have he : 8 * (bs.length + 1) = 8 * bs.length + 8 := by omega
      rw [he, pow_add]
      norm_num
    have htailbig : (BitVec.fromLEBytes (bs.map U8.bv)).toNat <
        2 ^ (8 * (bs.length + 1)) := by
      rw [hpow]
      have hp : 0 < 2 ^ (8 * bs.length) := by positivity
      omega
    have hshift : (BitVec.fromLEBytes (bs.map U8.bv)).toNat <<< 8 <
        2 ^ (8 * (bs.length + 1)) := by
      rw [Nat.shiftLeft_eq, hpow]
      omega
    rw [Nat.mod_eq_of_lt hlarge, Nat.mod_eq_of_lt htailbig,
      Nat.mod_eq_of_lt hshift, Nat.or_comm,
      ← Nat.shiftLeft_add_eq_or_of_lt hb]
    rw [Nat.shiftLeft_eq, ih]
    omega

theorem leValue_append_singleton (bs : List U8) (b : U8) :
    leValue (bs ++ [b]) = leValue bs + 256 ^ bs.length * b.val := by
  induction bs with
  | nil => simp [leValue]
  | cons c cs ih =>
    simp only [List.cons_append, List.length_cons, leValue, ih, pow_succ]
    ring

theorem leValue_reverse (bs : List U8) :
    leValue bs.reverse = bytesValue bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.reverse_cons, leValue_append_singleton, ih, bytesValue]
    simp only [List.length_reverse]
    ac_rfl

theorem fromBEValue (bs : List U8) :
    (BitVec.fromBEBytes (bs.map U8.bv)).toNat = bytesValue bs := by
  unfold BitVec.fromBEBytes
  rw [BitVec.toNat_cast]
  rw [← List.map_reverse, fromLEValue, leValue_reverse]

end AddressConversions

namespace AddressConversions

/-- The pinned unsigned conversion reads fixed-width octets in network order. -/
theorem u32_from_be_bytes_value (octets : Aeneas.Std.Array Aeneas.Std.U8 4#usize) :
    (Aeneas.Std.core.num.U32.from_be_bytes octets).val =
      CidrModel.bytesValue octets.val := by
  simp only [Aeneas.Std.core.num.U32.from_be_bytes]
  exact fromBEValue octets.val

theorem u128_from_be_bytes_value (octets : Aeneas.Std.Array Aeneas.Std.U8 16#usize) :
    (Aeneas.Std.core.num.U128.from_be_bytes octets).val =
      CidrModel.bytesValue octets.val := by
  simp only [Aeneas.Std.core.num.U128.from_be_bytes]
  exact fromBEValue octets.val

theorem ipv4_to_bits_spec (ip : ipnet.core.net.ip_addr.Ipv4Addr) :
    ∃ out, ipnet.core.net.ip_addr.Ipv4Addr.to_bits ip = Aeneas.Std.Result.ok out ∧
      out.val = CidrModel.ipv4Value ip := by
  refine ⟨Aeneas.Std.core.num.U32.from_be_bytes ip.octets, rfl, ?_⟩
  exact u32_from_be_bytes_value ip.octets

theorem ipv6_to_bits_spec (ip : ipnet.core.net.ip_addr.Ipv6Addr) :
    ∃ out, ipnet.core.net.ip_addr.Ipv6Addr.to_bits ip = Aeneas.Std.Result.ok out ∧
      out.val = CidrModel.ipv6Value ip := by
  refine ⟨Aeneas.Std.core.num.U128.from_be_bytes ip.octets, rfl, ?_⟩
  exact u128_from_be_bytes_value ip.octets

theorem ipv4_into_u32_spec (ip : ipnet.core.net.ip_addr.Ipv4Addr) :
    ∃ out, ipnet.U32.Insts.CoreConvertFromIpv4Addr.from ip = Aeneas.Std.Result.ok out ∧
      out.val = CidrModel.ipv4Value ip := by
  simpa only [ipnet.U32.Insts.CoreConvertFromIpv4Addr.from] using ipv4_to_bits_spec ip

theorem ipv6_into_u128_spec (ip : ipnet.core.net.ip_addr.Ipv6Addr) :
    ∃ out, ipnet.U128.Insts.CoreConvertFromIpv6Addr.from ip = Aeneas.Std.Result.ok out ∧
      out.val = CidrModel.ipv6Value ip := by
  simpa only [ipnet.U128.Insts.CoreConvertFromIpv6Addr.from] using ipv6_to_bits_spec ip

theorem be_roundtrip (w : Nat) (h : w % 8 = 0) (x : BitVec w) :
    (BitVec.fromBEBytes x.toBEBytes).toNat = x.toNat := by
  unfold BitVec.fromBEBytes BitVec.toBEBytes
  simp only [BitVec.toNat_cast]
  rw [List.reverse_reverse, BitVec.fromLEBytes_toLEBytes h]
  simp

theorem u32_to_be_bytes_value (bits : Aeneas.Std.U32) :
    CidrModel.bytesValue (Aeneas.Std.core.num.U32.to_be_bytes bits).val = bits.val := by
  have h := fromBEValue (bits.bv.toBEBytes.map (@Aeneas.Std.UScalar.mk Aeneas.Std.UScalarTy.U8))
  have hmap : ((bits.bv.toBEBytes.map (@Aeneas.Std.UScalar.mk Aeneas.Std.UScalarTy.U8)).map Aeneas.Std.U8.bv) =
      bits.bv.toBEBytes := by
    simp [List.map_map, Function.comp_def]
  rw [hmap, be_roundtrip 32 (by decide)] at h
  simpa only [Aeneas.Std.core.num.U32.to_be_bytes, Aeneas.Std.Array.from_val,
    Aeneas.Std.U32.bv_toNat] using h.symm

theorem u128_to_be_bytes_value (bits : Aeneas.Std.U128) :
    CidrModel.bytesValue (Aeneas.Std.core.num.U128.to_be_bytes bits).val = bits.val := by
  have h := fromBEValue (bits.bv.toBEBytes.map (@Aeneas.Std.UScalar.mk Aeneas.Std.UScalarTy.U8))
  have hmap : ((bits.bv.toBEBytes.map (@Aeneas.Std.UScalar.mk Aeneas.Std.UScalarTy.U8)).map Aeneas.Std.U8.bv) =
      bits.bv.toBEBytes := by
    simp [List.map_map, Function.comp_def]
  rw [hmap, be_roundtrip 128 (by decide)] at h
  simpa only [Aeneas.Std.core.num.U128.to_be_bytes, Aeneas.Std.Array.from_val,
    Aeneas.Std.U128.bv_toNat] using h.symm

theorem ipv4_from_bits_spec (bits : Aeneas.Std.U32) :
    ∃ out, ipnet.core.net.ip_addr.Ipv4Addr.from_bits bits = Aeneas.Std.Result.ok out ∧
      CidrModel.ipv4Value out = bits.val := by
  refine ⟨{ octets := Aeneas.Std.core.num.U32.to_be_bytes bits }, ?_, ?_⟩
  · simp [ipnet.core.net.ip_addr.Ipv4Addr.from_bits, Aeneas.Std.lift]
  · exact u32_to_be_bytes_value bits

theorem ipv6_from_bits_spec (bits : Aeneas.Std.U128) :
    ∃ out, ipnet.core.net.ip_addr.Ipv6Addr.from_bits bits = Aeneas.Std.Result.ok out ∧
      CidrModel.ipv6Value out = bits.val := by
  refine ⟨{ octets := Aeneas.Std.core.num.U128.to_be_bytes bits }, ?_, ?_⟩
  · simp [ipnet.core.net.ip_addr.Ipv6Addr.from_bits, Aeneas.Std.lift]
  · exact u128_to_be_bytes_value bits

theorem ipv4_from_u32_spec (bits : Aeneas.Std.U32) :
    ∃ out, ipnet.core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from bits =
      Aeneas.Std.Result.ok out ∧ CidrModel.ipv4Value out = bits.val := by
  simpa only [ipnet.core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from] using
    ipv4_from_bits_spec bits

theorem ipv6_from_u128_spec (bits : Aeneas.Std.U128) :
    ∃ out, ipnet.core.net.ip_addr.Ipv6Addr.Insts.CoreConvertFromU128.from bits =
      Aeneas.Std.Result.ok out ∧ CidrModel.ipv6Value out = bits.val := by
  simpa only [ipnet.core.net.ip_addr.Ipv6Addr.Insts.CoreConvertFromU128.from] using
    ipv6_from_bits_spec bits

end AddressConversions
