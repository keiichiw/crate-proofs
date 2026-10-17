module
public import Proofs.AddressConversions
public import Proofs.OrderMath

public section

namespace Comparisons

open Aeneas Aeneas.Std

/-- The pinned array-to-slice model preserves the complete octet sequence. -/
theorem array_to_slice_val {α : Type u} {n : Usize} (a : Array α n) :
    (Array.to_slice a).val = a.val := by
  simp [Array.to_slice]

/-- The external scalar comparator model returns the independent network-order value comparison. -/
theorem ipv4_cmp_spec (a b : ipnet.core.net.ip_addr.Ipv4Addr) :
    ipnet.core.net.ip_addr.Ipv4Addr.Insts.CoreCmpOrd.cmp a b =
      Result.ok (compare (CidrModel.ipv4Value a) (CidrModel.ipv4Value b)) := by
  simp only [ipnet.core.net.ip_addr.Ipv4Addr.Insts.CoreCmpOrd.cmp,
    CidrModel.ipv4Value, AddressConversions.u32_from_be_bytes_value]

/-- Within the model, scalar order also equals lexicographic order of the slice octets. -/
theorem ipv4_cmp_slice_lex_spec (a b : ipnet.core.net.ip_addr.Ipv4Addr) :
    ipnet.core.net.ip_addr.Ipv4Addr.Insts.CoreCmpOrd.cmp a b =
      Result.ok (OrderMath.lexCompare
        ((Array.to_slice a.octets).val.map UScalar.val)
        ((Array.to_slice b.octets).val.map UScalar.val)) := by
  rw [ipv4_cmp_spec]
  have hlen : a.octets.val.length = b.octets.val.length := by
    simp
  have hlex := OrderMath.byte_lexCompare_eq_value a.octets.val b.octets.val hlen
  simp only [array_to_slice_val, CidrModel.ipv4Value, hlex]

/-- The extracted Rust `partial_cmp` body succeeds and always returns `some`. -/
theorem ipv4_partial_cmp_spec (a b : ipnet.core.net.ip_addr.Ipv4Addr) :
    ipnet.core.net.ip_addr.Ipv4Addr.Insts.CoreCmpPartialOrdIpv4Addr.partial_cmp a b =
      Result.ok (some (compare (CidrModel.ipv4Value a) (CidrModel.ipv4Value b))) := by
  simp [ipnet.core.net.ip_addr.Ipv4Addr.Insts.CoreCmpPartialOrdIpv4Addr.partial_cmp,
    ipv4_cmp_spec, bind_ok]

private theorem compare_le_decide (x y : Nat) :
    (decide (compare x y = Ordering.lt) || decide (x = y)) = decide (x ≤ y) := by
  cases h : compare x y with
  | lt =>
    have hxy := Nat.compare_eq_lt.mp h
    simp [Nat.le_of_lt hxy]
  | eq =>
    have hxy := Nat.compare_eq_eq.mp h
    simp [hxy]
  | gt =>
    have hxy := Nat.compare_eq_gt.mp h
    have hne : x ≠ y := by omega
    have hnle : ¬ x ≤ y := by omega
    simp [hne, hnle]

/-- The selected Aeneas default `PartialOrd::le` model, applied to the extracted
    `partial_cmp`, succeeds with the usual numeric order. -/
theorem ipv4_le_spec (a b : ipnet.core.net.ip_addr.Ipv4Addr) :
    (ipnet.core.net.ip_addr.Ipv4Addr.Insts.CoreCmpPartialOrdIpv4Addr.le a b) =
      Result.ok (decide (CidrModel.ipv4Value a ≤ CidrModel.ipv4Value b)) := by
  simp only [core.cmp.PartialOrd.le.default,
    core.cmp.PartialOrd.le_body, ipv4_partial_cmp_spec]
  simp [compare_le_decide]

/-- The IPv6 scalar comparator model returns the independent network-order value comparison. -/
theorem ipv6_cmp_spec (a b : ipnet.core.net.ip_addr.Ipv6Addr) :
    ipnet.core.net.ip_addr.Ipv6Addr.Insts.CoreCmpOrd.cmp a b =
      Result.ok (compare (CidrModel.ipv6Value a) (CidrModel.ipv6Value b)) := by
  simp only [ipnet.core.net.ip_addr.Ipv6Addr.Insts.CoreCmpOrd.cmp,
    CidrModel.ipv6Value, AddressConversions.u128_from_be_bytes_value]

/-- Byte-lexicographic interpretation of the IPv6 scalar comparison model. -/
theorem ipv6_cmp_slice_lex_spec (a b : ipnet.core.net.ip_addr.Ipv6Addr) :
    ipnet.core.net.ip_addr.Ipv6Addr.Insts.CoreCmpOrd.cmp a b =
      Result.ok (OrderMath.lexCompare
        ((Array.to_slice a.octets).val.map UScalar.val)
        ((Array.to_slice b.octets).val.map UScalar.val)) := by
  rw [ipv6_cmp_spec]
  have hlen : a.octets.val.length = b.octets.val.length := by
    simp
  have hlex := OrderMath.byte_lexCompare_eq_value a.octets.val b.octets.val hlen
  simp only [array_to_slice_val, CidrModel.ipv6Value, hlex]

/-- The extracted Rust IPv6 `partial_cmp` body succeeds and always returns `some`. -/
theorem ipv6_partial_cmp_spec (a b : ipnet.core.net.ip_addr.Ipv6Addr) :
    ipnet.core.net.ip_addr.Ipv6Addr.Insts.CoreCmpPartialOrdIpv6Addr.partial_cmp a b =
      Result.ok (some (compare (CidrModel.ipv6Value a) (CidrModel.ipv6Value b))) := by
  simp [ipnet.core.net.ip_addr.Ipv6Addr.Insts.CoreCmpPartialOrdIpv6Addr.partial_cmp,
    ipv6_cmp_spec, bind_ok]

/-- The selected Aeneas default IPv6 `PartialOrd::le` model, applied to the
    extracted `partial_cmp`, succeeds with numeric order. -/
theorem ipv6_le_spec (a b : ipnet.core.net.ip_addr.Ipv6Addr) :
    (ipnet.core.net.ip_addr.Ipv6Addr.Insts.CoreCmpPartialOrdIpv6Addr.le a b) =
      Result.ok (decide (CidrModel.ipv6Value a ≤ CidrModel.ipv6Value b)) := by
  simp only [core.cmp.PartialOrd.le.default,
    core.cmp.PartialOrd.le_body, ipv6_partial_cmp_spec]
  simp [compare_le_decide]

end Comparisons
