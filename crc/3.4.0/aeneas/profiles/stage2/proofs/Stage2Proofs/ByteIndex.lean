import Stage2Proofs.ByteMathWide
import Stage2Proofs.ReflectMathWide
namespace CrcByteIndex

theorem masked_shift {N : Nat} (hN : 8 ≤ N) (word : BitVec N) :
    (word &&& 255) <<< (N-8) = word <<< (N-8) := by
  rw [← CrcReflectedWide.lowByte_mask]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hs : N-8 ≤ i
  · have hb : i-(N-8) < 8 := by omega
    have hbN : i-(N-8) < N := by omega
    simp [CrcReflectedWide.lowByte, hi, hs, hb, hbN, ← BitVec.getLsbD_eq_getElem]
  · have hsmall : i < N-8 := by omega
    simp [CrcReflectedWide.lowByte, hi, hs, hsmall, ← BitVec.getLsbD_eq_getElem]

theorem aligned_index {N : Nat} (hN : 8 ≤ N) (state : BitVec N) (byte : BitVec 8) :
    ((((state >>> (N-8)) ^^^ byte.setWidth N) &&& 255) <<< (N-8)) =
      CrcCanonicalWide.highPart state ^^^ CrcCanonicalWide.encodeByte N byte := by
  rw [masked_shift hN, BitVec.shiftLeft_xor_distrib]
  rfl

theorem reflected_index {N : Nat} (hN : 8 ≤ N) (state : BitVec N) (byte : BitVec 8) :
    ((state ^^^ byte.setWidth N) &&& 255) = (state &&& 255) ^^^ byte.setWidth N := by
  rw [← CrcReflectedWide.lowByte_mask, ← CrcReflectedWide.lowByte_mask]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hb : i < 8
  · simp [CrcReflectedWide.lowByte, hi, hb]
  · have hz := BitVec.getLsbD_of_ge byte i (by omega)
    simp [CrcReflectedWide.lowByte, hi, hb, hz]

theorem shifted_xor_byte {N : Nat} (state : BitVec N) (byte : BitVec 8) :
    ((state ^^^ byte.setWidth N) >>> 8) = state >>> 8 := by
  rw [BitVec.ushiftRight_xor_distrib]
  have hz : (byte.setWidth N >>> 8) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hb : byte.getLsbD (8+i) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    simp [hb]
  rw [hz]
  simp

theorem shifted_xor_encoded {N : Nat} (hN : 8 ≤ N) (state : BitVec N) (byte : BitVec 8) :
    ((state ^^^ CrcCanonicalWide.encodeByte N byte) <<< 8) = state <<< 8 := by
  rw [BitVec.shiftLeft_xor_distrib]
  have hz : (CrcCanonicalWide.encodeByte N byte <<< 8) = 0 := by
    simp [CrcCanonicalWide.encodeByte, ← BitVec.shiftLeft_add, Nat.sub_add_cancel hN]
  rw [hz]
  simp

theorem highPart_encoded {N : Nat} (hN : 8 ≤ N) (byte : BitVec 8) :
    CrcCanonicalWide.highPart (CrcCanonicalWide.encodeByte N byte) = CrcCanonicalWide.encodeByte N byte := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hs : N-8 ≤ i
  · have hb : i-(N-8) < 8 := by omega
    have hidx : N-8+(i-(N-8)) = i := by omega
    simp [CrcCanonicalWide.highPart, CrcCanonicalWide.encodeByte, hi, hs, hb, hidx,
      show ¬i < N-8 by omega, ← BitVec.getLsbD_eq_getElem]
  · have hsmall : i < N-8 := by omega
    simp [CrcCanonicalWide.highPart, CrcCanonicalWide.encodeByte, hi, hsmall]

theorem highPart_injected {N : Nat} (hN : 8 ≤ N) (state : BitVec N) (byte : BitVec 8) :
    CrcCanonicalWide.highPart (state ^^^ CrcCanonicalWide.encodeByte N byte) =
      ((((state >>> (N-8)) ^^^ byte.setWidth N) &&& 255) <<< (N-8)) := by
  rw [aligned_index hN]
  unfold CrcCanonicalWide.highPart
  rw [BitVec.ushiftRight_xor_distrib, BitVec.shiftLeft_xor_distrib]
  exact congrArg (fun x : BitVec N => ((state >>> (N-8)) <<< (N-8)) ^^^ x) (highPart_encoded hN byte)
end CrcByteIndex
