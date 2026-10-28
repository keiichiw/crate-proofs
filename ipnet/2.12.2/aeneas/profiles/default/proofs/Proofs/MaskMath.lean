module
public import Ipnet

public section

open Aeneas Aeneas.Std

namespace MaskMath

theorem max_shiftLeft_value (w s : Nat) (hs : s ≤ w) :
    ((BitVec.ofNat w (2 ^ w - 1)).shiftLeft s).toNat = 2 ^ w - 2 ^ s := by
  rw [BitVec.shiftLeft_eq, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  have hw : 0 < 2 ^ w := by positivity
  have hmax : (2 ^ w - 1) % 2 ^ w = 2 ^ w - 1 :=
    Nat.mod_eq_of_lt (by omega)
  rw [hmax, Nat.shiftLeft_eq, Nat.sub_mul]
  have hspos : 0 < 2 ^ s := by positivity
  have hpow : 2 ^ s ≤ 2 ^ w := by gcongr
  have hx : 2 ^ s - 1 < 2 ^ w * 2 ^ s := by
    have hm := Nat.mul_le_mul_right (2 ^ s) hw
    omega
  have hm := Nat.mul_sub_mod (n := 2 ^ w) (p := 2 ^ s) (x := 2 ^ s - 1) hx
  have hsmall : 2 ^ s - 1 < 2 ^ w := by omega
  rw [Nat.mod_eq_of_lt hsmall] at hm
  simpa [Nat.sub_add_cancel hspos] using hm

theorem max_ushiftRight_value (w p : Nat) (hp : p ≤ w) :
    ((BitVec.ofNat w (2 ^ w - 1)).ushiftRight p).toNat = 2 ^ (w - p) - 1 := by
  rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hw : 0 < 2 ^ w := by positivity
  have hmax : (2 ^ w - 1) % 2 ^ w = 2 ^ w - 1 :=
    Nat.mod_eq_of_lt (by omega)
  rw [hmax]
  have hwp : 2 ^ w = 2 ^ p * 2 ^ (w - p) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hwp]
  have h := Nat.mul_sub_div 0 (2 ^ p) (2 ^ (w - p)) (by positivity)
  simpa using h

end MaskMath
