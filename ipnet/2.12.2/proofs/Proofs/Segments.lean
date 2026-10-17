module
public import Proofs.OrderMath

public section

namespace Segments

open Aeneas.Std

/-- The value of one IPv6 segment after `from_be`, in network byte order. -/
@[expose] def pairValue (hi lo : U8) : Nat := 256 * hi.val + lo.val

@[expose] def pairedBytes : List (U8 × U8) → List U8
  | [] => []
  | (hi, lo) :: rest => hi :: lo :: pairedBytes rest

@[expose] def segmentDigits (pairs : List (U8 × U8)) : List Nat :=
  pairs.map (fun p => pairValue p.1 p.2)

@[expose] def pairsOfBytes : List U8 → List (U8 × U8)
  | hi :: lo :: rest => (hi, lo) :: pairsOfBytes rest
  | _ => []

theorem pairedBytes_pairsOfBytes (bs : List U8)
    (heven : bs.length % 2 = 0) : pairedBytes (pairsOfBytes bs) = bs := by
  induction bs using List.twoStepInduction with
  | nil => rfl
  | singleton x => simp at heven
  | cons_cons hi lo rest ih _ =>
    have hrest : rest.length % 2 = 0 := by
      have hlen : (hi :: lo :: rest).length = rest.length + 2 := by simp
      rw [hlen] at heven
      omega
    simp [pairsOfBytes, pairedBytes, ih hrest]

theorem pairValue_bound (hi lo : U8) : pairValue hi lo < 65536 := by
  have hhi := U8.lt_succ_max hi
  have hlo := U8.lt_succ_max lo
  unfold pairValue
  omega

theorem pairedBytes_length (pairs : List (U8 × U8)) :
    (pairedBytes pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨hi, lo⟩
    simp [pairedBytes, ih]
    omega

theorem segmentDigits_length (pairs : List (U8 × U8)) :
    (segmentDigits pairs).length = pairs.length := by
  simp [segmentDigits]

theorem segmentDigits_bound (pairs : List (U8 × U8)) :
    ∀ d ∈ segmentDigits pairs, d < 65536 := by
  intro d hd
  obtain ⟨pair, _, rfl⟩ := List.mem_map.mp hd
  exact pairValue_bound pair.1 pair.2

/-- Pairing network-order octets into 16-bit words preserves the address value. -/
theorem segmentDigits_value (pairs : List (U8 × U8)) :
    OrderMath.digitsValue 65536 (segmentDigits pairs) =
      CidrModel.bytesValue (pairedBytes pairs) := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨hi, lo⟩
    have hpow : 256 ^ (2 * rest.length) = 65536 ^ rest.length := by
      have h : 256 ^ (2 * rest.length) = (256 ^ 2) ^ rest.length := by
        rw [pow_mul]
      simpa using h
    simp only [segmentDigits, List.map_cons, OrderMath.digitsValue,
      List.length_map, pairedBytes, CidrModel.bytesValue,
      List.length_cons, pairedBytes_length]
    rw [show 2 * rest.length + 1 = (2 * rest.length) + 1 by omega, pow_succ,
      hpow]
    norm_num [pairValue]
    have htail : OrderMath.digitsValue 65536
        (List.map (fun p => 256 * ↑p.1 + ↑p.2) rest) =
        CidrModel.bytesValue (pairedBytes rest) := by
      simpa [segmentDigits, pairValue] using ih
    rw [htail]
    ring

theorem segmentDigits_value_even (bs : List U8)
    (heven : bs.length % 2 = 0) :
    OrderMath.digitsValue 65536 (segmentDigits (pairsOfBytes bs)) =
      CidrModel.bytesValue bs := by
  rw [segmentDigits_value, pairedBytes_pairsOfBytes bs heven]

theorem ipv6_segmentDigits_length (ip : ipnet.core.net.ip_addr.Ipv6Addr) :
    (segmentDigits (pairsOfBytes ip.octets.val)).length = 8 := by
  have hlen : ip.octets.val.length = 16 := by
    exact Array.property ip.octets
  have heven : ip.octets.val.length % 2 = 0 := by simp [hlen]
  have hpair := pairedBytes_pairsOfBytes ip.octets.val heven
  have htwice := pairedBytes_length (pairsOfBytes ip.octets.val)
  rw [segmentDigits_length]
  rw [hpair] at htwice
  omega

theorem ipv6_segmentDigits_value (ip : ipnet.core.net.ip_addr.Ipv6Addr) :
    OrderMath.digitsValue 65536 (segmentDigits (pairsOfBytes ip.octets.val)) =
      CidrModel.ipv6Value ip := by
  have hlen : ip.octets.val.length = 16 := by
    exact Array.property ip.octets
  have heven : ip.octets.val.length % 2 = 0 := by simp [hlen]
  exact segmentDigits_value_even ip.octets.val heven

end Segments
