module
public import Proofs.AddressConversions

public section

open Aeneas Aeneas.Std

namespace IPv4AddressEq

theorem bytesValue_injective_same_length (xs ys : List U8)
    (hlen : xs.length = ys.length)
    (heq : CidrModel.bytesValue xs = CidrModel.bytesValue ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hlen' : xs.length = ys.length := by simpa using hlen
          have hpow : 256 ^ xs.length = 256 ^ ys.length := by rw [hlen']
          have hxBound := CidrModel.bytesValue_bound xs
          have hyBound := CidrModel.bytesValue_bound ys
          have hrem : CidrModel.bytesValue xs = CidrModel.bytesValue ys := by
            have hm := congrArg (fun z => z % 256 ^ xs.length) heq
            have hyBound' : CidrModel.bytesValue ys < 256 ^ xs.length := by
              simpa [hlen'] using hyBound
            simp only [CidrModel.bytesValue] at hm
            rw [← hlen'] at hm
            simp only [Nat.mul_add_mod_self_right,
              Nat.mod_eq_of_lt hxBound,
              Nat.mod_eq_of_lt hyBound'] at hm
            exact hm
          have hprod : x.val * 256 ^ xs.length =
              y.val * 256 ^ xs.length := by
            simp only [CidrModel.bytesValue, ← hlen'] at heq
            omega
          have hval : x.val = y.val :=
            Nat.eq_of_mul_eq_mul_right (by positivity) hprod
          have hxy : x = y := UScalar.eq_of_val_eq hval
          have ht := ih ys hlen' hrem
          simp [hxy, ht]

theorem ipv4Value_injective (a b : ipnet.core.net.ip_addr.Ipv4Addr)
    (h : CidrModel.ipv4Value a = CidrModel.ipv4Value b) : a = b := by
  have hlen : a.octets.val.length = b.octets.val.length := by
    have ha := Aeneas.Std.Array.property a.octets
    have hb := Aeneas.Std.Array.property b.octets
    omega
  have hlist : a.octets.val = b.octets.val :=
    bytesValue_injective_same_length _ _ hlen h
  have harray : a.octets = b.octets :=
    Aeneas.Std.Array.ext _ _ hlist
  cases a
  cases b
  simp_all

theorem ipv4Value_eq_iff (a b : ipnet.core.net.ip_addr.Ipv4Addr) :
    CidrModel.ipv4Value a = CidrModel.ipv4Value b ↔ a = b := by
  exact ⟨ipv4Value_injective a b, by intro h; rw [h]⟩

end IPv4AddressEq
