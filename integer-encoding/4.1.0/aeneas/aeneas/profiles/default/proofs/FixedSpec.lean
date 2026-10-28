import Aeneas
open Aeneas Aeneas.Std
namespace IntegerEncodingSpec

def fixedBytes (m n : Nat) : List Nat := (List.range m).map (fun i => n / 256 ^ i % 256)

theorem toLEBytes_arithmetic {w : Nat} (x : BitVec w) :
    x.toLEBytes.map (fun b => b.toNat) = fixedBytes ((w+7)/8) x.toNat := by
  apply List.ext_getElem
  · simp [fixedBytes]
  intro i h₁ h₂
  simp only [List.length_map] at h₁
  simp only [List.getElem_map, fixedBytes, List.getElem_range]
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 8
  · have hbit := BitVec.toLEBytes_getElem!_testBit x i j hj
    rw [← List.Inhabited_getElem_eq_getElem! _ _ h₁] at hbit
    change (x.toLEBytes[i].toNat).testBit j = _ at hbit
    rw [hbit]
    rw [BitVec.getElem!_eq_testBit_toNat]
    rw [show 256^i=2^(8*i) by rw [Nat.pow_mul]]
    rw [show 256=2^8 by rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp only [hj, decide_true, Bool.true_and]
    congr 1
    omega
  · have hb : x.toLEBytes[i].toNat < 2^8 := (x.toLEBytes[i]).isLt
    have hd : x.toNat / 256^i % 256 < 2^8 := Nat.mod_lt _ (by decide)
    have := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 ≤ j)))
    have := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hd (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 ≤ j)))
    simp_all
def fixedValue (bs : List Nat) : Nat := bs.foldr (fun b n => b + 256*n) 0

theorem fromLEBytes_arithmetic (bs : List Byte) :
    (BitVec.fromLEBytes bs).toNat = fixedValue (bs.map (fun b => b.toNat)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hlo : b.toNat < 2^(8*(b::bs).length) := by
      have h : 2^8 ≤ 2^(8*(b::bs).length) := Nat.pow_le_pow_right (by decide) (by simp)
      exact Nat.lt_of_lt_of_le b.isLt h
    have hmid : (BitVec.fromLEBytes bs).toNat < 2^(8*(b::bs).length) := by
      exact Nat.lt_of_lt_of_le (BitVec.fromLEBytes bs).isLt (Nat.pow_le_pow_right (by decide) (by simp))
    have hshift : (BitVec.fromLEBytes bs).toNat * 2^8 < 2^(8*(b::bs).length) := by
      have hp : 8*(b::bs).length=8*bs.length+8 := by simp; omega
      rw [hp, Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right (BitVec.fromLEBytes bs).isLt (by decide)
    simp only [BitVec.fromLEBytes, BitVec.toNat_or, BitVec.toNat_setWidth,
      BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hmid,
      Nat.mod_eq_of_lt hshift]
    rw [Nat.or_comm, Nat.mul_comm (BitVec.fromLEBytes bs).toNat (2^8), ← Nat.two_pow_add_eq_or_of_lt b.isLt]
    simp only [Nat.reducePow, List.map_cons, fixedValue, List.foldr_cons] at *
    rw [ih]
    omega

def signedValue (w n : Nat) : Int :=
  if 2*n < 2^w then (n : Int) else (n : Int) - (2^w : Nat)

theorem toInt_arithmetic {w : Nat} (x : BitVec w) :
    x.toInt = signedValue w x.toNat := by
  exact BitVec.toInt_eq_toNat_cond x

theorem fromLEBytes_signed (bs : List Byte) :
    (BitVec.fromLEBytes bs).toInt =
      signedValue (8*bs.length) (fixedValue (bs.map (fun b => b.toNat))) := by
  rw [toInt_arithmetic, fromLEBytes_arithmetic]

end IntegerEncodingSpec
