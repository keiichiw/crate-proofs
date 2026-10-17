module
public import Ipnet

public section

/- Independent, unbounded arithmetic for valid CIDR prefixes. These definitions
make no reference to the extracted `ipnet` implementation. -/
namespace CidrModel

open Aeneas.Std

/-- Network-order interpretation of octets, independent of integer conversion APIs. -/
@[expose] def bytesValue : List U8 → Nat
  | [] => 0
  | b :: rest => b.val * 256 ^ rest.length + bytesValue rest

theorem bytesValue_bound (bytes : List U8) :
    bytesValue bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp [bytesValue]
  | cons b rest ih =>
    have hb := U8.le_max b
    have hm := Nat.mul_le_mul_right (256 ^ rest.length) hb
    simp only [bytesValue, List.length_cons, pow_succ]
    omega

@[expose] def ipv4Value (ip : ipnet.core.net.ip_addr.Ipv4Addr) : Nat :=
  bytesValue ip.octets.val

@[expose] def ipv6Value (ip : ipnet.core.net.ip_addr.Ipv6Addr) : Nat :=
  bytesValue ip.octets.val

theorem ipv4Value_bound (ip : ipnet.core.net.ip_addr.Ipv4Addr) :
    ipv4Value ip < 2 ^ 32 := by
  have h := bytesValue_bound ip.octets.val
  have hlen := Aeneas.Std.Array.property ip.octets
  simp only [ipv4Value] at *
  norm_num at hlen
  simpa [hlen] using h

theorem ipv6Value_bound (ip : ipnet.core.net.ip_addr.Ipv6Addr) :
    ipv6Value ip < 2 ^ 128 := by
  have h := bytesValue_bound ip.octets.val
  have hlen := Aeneas.Std.Array.property ip.octets
  simp only [ipv6Value] at *
  norm_num at hlen
  simpa [hlen] using h

@[expose] def size (w p : Nat) : Nat := 2 ^ (w - p)
@[expose] def lower (w a p : Nat) : Nat := (a / size w p) * size w p
@[expose] def upper (w a p : Nat) : Nat := lower w a p + size w p - 1
@[expose] def member (w a p x : Nat) : Prop := lower w a p ≤ x ∧ x ≤ upper w a p
@[expose] def subset (w a p b q : Nat) : Prop := ∀ x, member w b q x → member w a p x
@[expose] def taggedMember (family w a p : Nat) (tagged : Nat × Nat) : Prop :=
  tagged.1 = family ∧ member w a p tagged.2
@[expose] def taggedSubset (family₁ w₁ a p family₂ w₂ b q : Nat) : Prop :=
  ∀ tagged, taggedMember family₂ w₂ b q tagged →
    taggedMember family₁ w₁ a p tagged

theorem size_pos (w p : Nat) : 0 < size w p := by
  simp [size]

theorem lower_le_address (w a p : Nat) : lower w a p ≤ a := by
  unfold lower
  exact Nat.div_mul_le_self a (size w p)

theorem address_lt_lower_add_size (w a p : Nat) : a < lower w a p + size w p := by
  have h := Nat.mod_lt a (size_pos w p)
  have hdiv : a % size w p + (a / size w p) * size w p = a := by
    simpa [Nat.mul_comm] using Nat.mod_add_div a (size w p)
  unfold lower
  omega

theorem upper_eq (w a p : Nat) :
    upper w a p = lower w a p + (size w p - 1) := by
  unfold upper
  have h := size_pos w p
  omega

theorem lower_le_upper (w a p : Nat) : lower w a p ≤ upper w a p := by
  rw [upper_eq]
  omega

theorem address_le_upper (w a p : Nat) : a ≤ upper w a p := by
  have h := address_lt_lower_add_size w a p
  rw [upper_eq]
  have hp := size_pos w p
  omega

theorem address_mem (w a p : Nat) : member w a p a :=
  ⟨lower_le_address w a p, address_le_upper w a p⟩

theorem lower_mem (w a p : Nat) : member w a p (lower w a p) :=
  ⟨le_refl _, lower_le_upper w a p⟩

theorem upper_mem (w a p : Nat) : member w a p (upper w a p) :=
  ⟨lower_le_upper w a p, le_refl _⟩

theorem lower_add_size_le_width (w a p : Nat)
    (hp : p ≤ w) (ha : a < 2 ^ w) :
    lower w a p + size w p ≤ 2 ^ w := by
  have hpow : 2 ^ w = 2 ^ p * size w p := by
    have heq : p + (w - p) = w := by omega
    rw [size, ← pow_add, heq]
  have hq : a / size w p < 2 ^ p :=
    (Nat.div_lt_iff_lt_mul (size_pos w p)).2 (by rw [← hpow]; exact ha)
  have hm := Nat.mul_le_mul_right (size w p) (Nat.succ_le_iff.mpr hq)
  have hs : lower w a p + size w p = (a / size w p + 1) * size w p := by
    simp [lower, Nat.add_mul]
  rw [hs, hpow]
  simpa [Nat.add_mul] using hm

theorem upper_lt_width (w a p : Nat)
    (hp : p ≤ w) (ha : a < 2 ^ w) : upper w a p < 2 ^ w := by
  have h := lower_add_size_le_width w a p hp ha
  rw [upper_eq]
  have hs := size_pos w p
  omega

theorem lower_normalize (w a p : Nat) :
    lower w (lower w a p) p = lower w a p := by
  unfold lower
  have h : (a / size w p * size w p) / size w p = a / size w p := by
    rw [Nat.mul_comm, Nat.mul_div_cancel_left (a / size w p) (size_pos w p)]
  rw [h]

theorem upper_normalize (w a p : Nat) :
    upper w (lower w a p) p = upper w a p := by
  simp only [upper_eq, lower_normalize]

theorem member_normalize (w a p x : Nat) :
    member w (lower w a p) p x ↔ member w a p x := by
  simp only [member, lower_normalize, upper_normalize]

theorem upper_eq_of_lower_eq (w a b p : Nat)
    (h : lower w a p = lower w b p) : upper w a p = upper w b p := by
  simp only [upper_eq, h]

theorem member_eq_of_lower_eq (w a b p x : Nat)
    (h : lower w a p = lower w b p) :
    member w a p x ↔ member w b p x := by
  simp only [member, h, upper_eq_of_lower_eq w a b p h]

theorem subset_iff_endpoints (w a p b q : Nat) :
    subset w a p b q ↔
      lower w a p ≤ lower w b q ∧ upper w b q ≤ upper w a p := by
  constructor
  · intro h
    exact ⟨(h _ (lower_mem w b q)).1, (h _ (upper_mem w b q)).2⟩
  · rintro ⟨hlo, hhi⟩ x ⟨hxlo, hxhi⟩
    exact ⟨le_trans hlo hxlo, le_trans hxhi hhi⟩

theorem tagged_subset_iff (family₁ w₁ a p family₂ w₂ b q : Nat) :
    taggedSubset family₁ w₁ a p family₂ w₂ b q ↔
      family₁ = family₂ ∧ lower w₁ a p ≤ lower w₂ b q ∧
        upper w₂ b q ≤ upper w₁ a p := by
  constructor
  · intro h
    have hlo := h (family₂, lower w₂ b q) ⟨rfl, lower_mem w₂ b q⟩
    have hhi := h (family₂, upper w₂ b q) ⟨rfl, upper_mem w₂ b q⟩
    exact ⟨hlo.1.symm, hlo.2.1, hhi.2.2⟩
  · rintro ⟨hfam, hlo, hhi⟩ ⟨tag, x⟩ ⟨htag, hxlo, hxhi⟩
    exact ⟨htag.trans hfam.symm, le_trans hlo hxlo, le_trans hxhi hhi⟩

theorem subset_refl (w a p : Nat) : subset w a p a p := by
  intro x hx
  exact hx

theorem subset_trans (w a p b q c r : Nat)
    (hab : subset w a p b q) (hbc : subset w b q c r) :
    subset w a p c r := by
  intro x hx
  exact hab x (hbc x hx)

theorem subset_normalize_left (w a p b q : Nat) :
    subset w (lower w a p) p b q ↔ subset w a p b q := by
  simp only [subset, member_normalize]

theorem subset_normalize_right (w a p b q : Nat) :
    subset w a p (lower w b q) q ↔ subset w a p b q := by
  simp only [subset, member_normalize]

theorem mutual_subset_iff_endpoints (w a p b q : Nat) :
    (subset w a p b q ∧ subset w b q a p) ↔
      lower w a p = lower w b q ∧ upper w a p = upper w b q := by
  simp only [subset_iff_endpoints]
  omega

theorem size_zero (w : Nat) : size w 0 = 2 ^ w := by
  simp [size]

theorem size_full (w : Nat) : size w w = 1 := by
  simp [size]

theorem lower_full (w a : Nat) : lower w a w = a := by
  simp [lower, size_full]

theorem upper_full (w a : Nat) : upper w a w = a := by
  simp [upper, lower_full, size_full]

theorem member_full (w a x : Nat) : member w a w x ↔ x = a := by
  simp [member, lower_full, upper_full]
  omega

theorem lower_zero (w a : Nat) (ha : a < 2 ^ w) : lower w a 0 = 0 := by
  simp [lower, size_zero, Nat.div_eq_of_lt ha]

theorem upper_zero (w a : Nat) (ha : a < 2 ^ w) :
    upper w a 0 = 2 ^ w - 1 := by
  simp [upper, lower_zero w a ha, size_zero]

theorem member_zero (w a x : Nat) (ha : a < 2 ^ w) :
    member w a 0 x ↔ x < 2 ^ w := by
  simp [member, lower_zero w a ha, upper_zero w a ha]
  have hpow : 0 < 2 ^ w := by positivity
  omega

end CidrModel
