import Stage2Proofs.ByteMathWide
namespace CrcWidthEncoding

/-- MSB-aligned physical register representation for a width-w canonical CRC state. -/
def encode {w : Nat} (N : Nat) (state : BitVec w) : BitVec N :=
  state.setWidth N <<< (N-w)

theorem encode_xor {w N : Nat} (a b : BitVec w) :
    encode N (a ^^^ b) = encode N a ^^^ encode N b := by
  simp only [encode, BitVec.setWidth_xor, BitVec.shiftLeft_xor_distrib]

theorem encode_msb {w N : Nat} (hw : 1 ≤ w) (hN : w ≤ N) (state : BitVec w) :
    (encode N state).getLsbD (N-1) = state.getLsbD (w-1) := by
  have ht : N-1 < N := by omega
  have hb : N-w ≤ N-1 := by omega
  have he : N-1-(N-w) = w-1 := by omega
  have hs : w-1 < w := by omega
  simp [encode, ht, hb, he, hs]

theorem encode_shift {w N : Nat} (hN : w ≤ N) (state : BitVec w) :
    encode N (state <<< 1) = encode N state <<< 1 := by
  unfold encode
  rw [← BitVec.shiftLeft_add]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlo : i < N-w
  · simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hi, hlo,
      show i < N-w+1 by omega]
  · have hbit : i-(N-w) < w := by omega
    by_cases hpos : N-w+1 ≤ i
    · have hind : i-(N-w)-1 = i-(N-w+1) := by omega
      simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hi, hlo, hbit,
        show ¬(i-(N-w)=0) by omega, show ¬(i≤N-w) by omega,
        show ¬i < N-w+1 by omega, show i-(N-w+1) < w by omega, hind]
    · have he : i = N-w := by omega
      subst i
      simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]

theorem encode_inputStep {w N : Nat} (hw : 1 ≤ w) (hN : w ≤ N)
    (poly state : BitVec w) (bit : Bool) :
    encode N (CrcCanonicalWide.inputStep poly state bit) =
      CrcCanonicalWide.inputStep (encode N poly) (encode N state) bit := by
  unfold CrcCanonicalWide.inputStep
  rw [encode_xor, encode_shift hN, encode_msb hw hN]
  cases h : state.getLsbD (w-1) != bit <;> simp [h, encode]

theorem encode_fold_bits {w N : Nat} (hw : 1 ≤ w) (hN : w ≤ N)
    (poly state : BitVec w) (bits : List Bool) :
    encode N (bits.foldl (CrcCanonicalWide.inputStep poly) state) =
      bits.foldl (CrcCanonicalWide.inputStep (encode N poly)) (encode N state) := by
  induction bits generalizing state with
  | nil => rfl
  | cons bit bits ih =>
    simp only [List.foldl_cons]
    rw [ih, encode_inputStep hw hN]

theorem encode_byteStep {w N : Nat} (hw : 1 ≤ w) (hN : w ≤ N)
    (poly state : BitVec w) (byte : BitVec 8) :
    encode N (CrcCanonicalWide.byteStep poly state byte) =
      CrcCanonicalWide.byteStep (encode N poly) (encode N state) byte :=
  encode_fold_bits hw hN poly state (CrcCanonical8.byteBits byte)

theorem encode_run {w N : Nat} (hw : 1 ≤ w) (hN : w ≤ N)
    (poly state : BitVec w) (bytes : List (BitVec 8)) :
    encode N (CrcCanonicalWide.run poly state bytes) =
      CrcCanonicalWide.run (encode N poly) (encode N state) bytes := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte bytes ih =>
    simp only [CrcCanonicalWide.run, List.foldl_cons] at *
    rw [ih, encode_byteStep hw hN]

end CrcWidthEncoding
