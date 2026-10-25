import Proofs.SignExtend
open Aeneas Aeneas.Std Result
/-! Arithmetic bridges for the safe variable-width reader proof.
These lemmas establish the scalar byte-conversion model and signed casts;
they do not by themselves verify any Buf reader or consumption behavior. -/
namespace bytes_numeric

theorem width_le_usize_max (n : Nat) (hn : n ≤ 8) : n ≤ Usize.max := by
  scalar_tac

theorem saturated_shortage_iff (len n : Nat) (hn : n ≤ 8) :
    Nat.min Usize.max len < n ↔ len < n := by
  have hm := width_le_usize_max n hn
  simp only [Nat.min_def]
  split <;> omega

theorem saturated_shortage_available (len n : Nat) (hn : n ≤ 8)
    (hshort : Nat.min Usize.max len < n) : Nat.min Usize.max len = len := by
  have hm := width_le_usize_max n hn
  simp only [Nat.min_def] at *
  split at hshort
  · omega
  · simp_all

def leValue : List U8 → Nat
  | [] => 0
  | b::bs => b.val + 256 * leValue bs
theorem fromLEBytes_value (bs : List U8) :
    (BitVec.fromLEBytes (bs.map U8.bv)).toNat = leValue bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.map_cons, BitVec.fromLEBytes.eq_2]
    simp only [List.length_cons,List.length_map,
      BitVec.toNat_or,BitVec.toNat_setWidth,BitVec.toNat_shiftLeft]
    have hb : b.bv.toNat < 2^8 := b.bv.isLt
    have ht := (BitVec.fromLEBytes (List.map U8.bv bs)).isLt
    simp only [List.length_map] at ht
    have hwidth : 2 ^ (8 * (bs.length + 1)) = 2 ^ (8 * bs.length) * 256 := by
      rw [Nat.mul_add,Nat.pow_add]
    have hbwidth : b.bv.toNat < 2 ^ (8 * (bs.length+1)) := by
      rw [hwidth]
      have hp : 0 < 2 ^ (8 * bs.length) := Nat.two_pow_pos _
      omega
    rw [Nat.mod_eq_of_lt hbwidth]
    have htwidth : (BitVec.fromLEBytes (List.map U8.bv bs)).toNat <<< 8 <
      2 ^ (8 * (bs.length+1)) := by
      rw [Nat.shiftLeft_eq,hwidth]
      omega
    have htwide : (BitVec.fromLEBytes (List.map U8.bv bs)).toNat < 2 ^ (8 * (bs.length+1)) := by
      rw [hwidth]
      omega
    rw [Nat.mod_eq_of_lt htwide,Nat.mod_eq_of_lt htwidth]
    rw [Nat.or_comm,← Nat.shiftLeft_add_eq_or_of_lt hb]
    rw [Nat.shiftLeft_eq,show 2^8=256 from rfl,ih]
    change leValue bs * 256 + b.val = b.val + 256 * leValue bs
    omega
theorem leValue_bound (bs : List U8) : leValue bs < 256^bs.length := by
  have h := (BitVec.fromLEBytes (bs.map U8.bv)).isLt
  rw [fromLEBytes_value] at h
  have hp : 2 ^ (8 * bs.length) = 256^bs.length := by
    rw [Nat.pow_mul]
  simpa only [List.length_map,hp] using h

def beValue (bs : List U8) : Nat := leValue bs.reverse

theorem fromBEBytes_value (bs : List U8) :
    (BitVec.fromBEBytes (bs.map U8.bv)).toNat = beValue bs := by
  unfold BitVec.fromBEBytes
  rw [BitVec.toNat_cast, ← List.map_reverse]
  simpa only [beValue] using fromLEBytes_value bs.reverse

theorem leValue_append (xs ys : List U8) :
    leValue (xs ++ ys) = leValue xs + 256^xs.length * leValue ys := by
  induction xs with
  | nil => simp [leValue]
  | cons x xs ih =>
    simp only [List.cons_append,leValue,ih,List.length_cons,Nat.pow_succ]
    ring

theorem leValue_zeros (n : Nat) : leValue (List.replicate n (0#u8)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,leValue,ih]

theorem leValue_pad (xs : List U8) (n : Nat) :
    leValue (xs ++ List.replicate n (0#u8)) = leValue xs := by
  rw [leValue_append,leValue_zeros]
  omega

theorem beValue_pad (xs : List U8) (n : Nat) :
    beValue (List.replicate n (0#u8) ++ xs) = beValue xs := by
  unfold beValue
  rw [List.reverse_append,List.reverse_replicate,leValue_pad]

theorem u64_from_le_bytes_value (a : Array U8 8#usize) :
    (core.num.U64.from_le_bytes a).val = leValue a.val := by
  change (BitVec.fromLEBytes (a.val.map U8.bv)).toNat = _
  exact fromLEBytes_value a.val

theorem u64_from_be_bytes_value (a : Array U8 8#usize) :
    (core.num.U64.from_be_bytes a).val = beValue a.val := by
  change (BitVec.fromBEBytes (a.val.map U8.bv)).toNat = _
  exact fromBEBytes_value a.val

/-- Interpretation of the full eight-byte scalar conversion, not signed
interpretation at a caller-selected short width. -/
def signed64 (v : Nat) : Int := if v < 2^63 then v else (v : Int) - 2^64

theorem signed64_short_leValue (bs : List U8) (hn : bs.length < 8) :
    signed64 (leValue bs) = (leValue bs : Int) := by
  have hb := leValue_bound bs
  have hp : 256^bs.length ≤ 256^7 := Nat.pow_le_pow_right (by omega) (by omega)
  have hv : leValue bs < 2^63 := by omega
  simp only [signed64,ite_eq_left hv]

theorem signed64_short_beValue (bs : List U8) (hn : bs.length < 8) :
    signed64 (beValue bs) = (beValue bs : Int) := by
  exact signed64_short_leValue bs.reverse (by simpa using hn)

theorem i64_from_le_bytes_value (a : Array U8 8#usize) :
    (core.num.I64.from_le_bytes a).val = signed64 (leValue a.val) := by
  change ((BitVec.fromLEBytes (a.val.map U8.bv)).cast (by simp)).toInt = _
  rw [BitVec.toInt_eq_toNat_cond,BitVec.toNat_cast]
  rw [fromLEBytes_value]
  change (if 2 * _ < 2^64 then _ else _) = _
  unfold signed64
  have h : 2*leValue a.val < 2^64 ↔ leValue a.val < 2^63 := by omega
  simp only [h]
  norm_num [IScalarTy.numBits]

theorem i64_from_be_bytes_value (a : Array U8 8#usize) :
    (core.num.I64.from_be_bytes a).val = signed64 (beValue a.val) := by
  change ((BitVec.fromBEBytes (a.val.map U8.bv)).cast (by simp)).toInt = _
  rw [BitVec.toInt_eq_toNat_cond,BitVec.toNat_cast]
  rw [fromBEBytes_value]
  change (if 2 * _ < 2^64 then _ else _) = _
  unfold signed64
  have h : 2*beValue a.val < 2^64 ↔ beValue a.val < 2^63 := by omega
  simp only [h]
  norm_num [IScalarTy.numBits]

theorem signedByteValue_leValue (bs : List U8) :
    bytes.signedByteValue (leValue bs) bs.length =
      if bs.length = 0 then 0
      else if leValue bs < 2^(8*bs.length-1) then (leValue bs : Int)
      else (leValue bs : Int) - (2^(8*bs.length) : Nat) := by
  have hb := leValue_bound bs
  have hp : 2^(8*bs.length) = 256^bs.length := by rw [Nat.pow_mul]
  unfold bytes.signedByteValue
  rw [hp,Nat.mod_eq_of_lt hb]

def signed8 (v : Nat) : Int := if v < 128 then v else (v : Int) - 256

theorem cast_i8_value (x : U8) : (UScalar.hcast .I8 x).val = signed8 x.val := by
  change (BitVec.setWidth 8 x.bv).toInt = signed8 x.val
  rw [BitVec.setWidth_eq,BitVec.toInt_eq_toNat_cond]
  simp only [signed8,show 2^8=256 from rfl]
  change (if 2*x.val < 256 then (x.val : Int) else (x.val : Int)-256) = _
  have h : 2*x.val < 256 ↔ x.val < 128 := by omega
  simp only [h]

end bytes_numeric
