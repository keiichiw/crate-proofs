import Stage2Proofs.ByteMath
open Aeneas Aeneas.Std
namespace CrcReflected8

def inputStep (poly state : BitVec 8) (bit : Bool) : BitVec 8 :=
  (state >>> 1) ^^^ (if state.getLsbD 0 != bit then poly else 0)

theorem reverse_xor (a b : BitVec 8) :
    (a ^^^ b).reverse = a.reverse ^^^ b.reverse := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_reverse, BitVec.getLsbD_xor,
    BitVec.getMsbD_eq_getLsbD, hi, decide_true, Bool.true_and]

theorem reverse_shiftLeft_one (a : BitVec 8) :
    (a <<< 1).reverse = a.reverse >>> 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight] <;> simp

theorem reverse_inputStep (poly state : BitVec 8) (bit : Bool) :
    (CrcCanonical8.inputStep poly state bit).reverse = inputStep poly.reverse state.reverse bit := by
  unfold CrcCanonical8.inputStep inputStep
  rw [reverse_xor, reverse_shiftLeft_one]
  have hb : state.reverse.getLsbD 0 = state.getLsbD 7 := by
    simp only [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD]; simp
  rw [hb]
  have hz : (0 : BitVec 8).reverse = 0 := BitVec.reverse_eq_zero_iff.mpr rfl
  cases h : state.getLsbD 7 != bit
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact congrArg (fun x : BitVec 8 => (state.reverse >>> 1) ^^^ x) hz
  · rfl
def byteBits (byte : BitVec 8) : List Bool :=
  [byte.getLsbD 0, byte.getLsbD 1, byte.getLsbD 2, byte.getLsbD 3,
   byte.getLsbD 4, byte.getLsbD 5, byte.getLsbD 6, byte.getLsbD 7]

/-- Canonical MSB register, with the input byte fed in reflected order. -/
def byteStep (poly state byte : BitVec 8) : BitVec 8 :=
  (byteBits byte).foldl (CrcCanonical8.inputStep poly) state

theorem byteStep_eq_reverse_byte (poly state byte : BitVec 8) :
    byteStep poly state byte = CrcCanonical8.byteStep poly state byte.reverse := by
  simp only [byteStep, byteBits, CrcCanonical8.byteStep, CrcCanonical8.byteBits,
    BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD]
  rfl

theorem reverse_polynomialStep (poly state : BitVec 8) :
    (crc.polynomialStep poly state false).reverse =
      crc.polynomialStep poly.reverse state.reverse true := by
  have h := reverse_inputStep poly state false
  simpa only [CrcCanonical8.inputStep, inputStep, crc.polynomialStep,
    Bool.bne_false, Bool.false_eq_true, ↓reduceIte] using h

theorem reverse_polynomialRun (poly state : BitVec 8) (n : Nat) :
    (crc.polynomialRun poly false n state).reverse =
      crc.polynomialRun poly.reverse true n state.reverse := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
    simp only [crc.polynomialRun]
    exact (ih _).trans (congrArg (crc.polynomialRun poly.reverse true n)
      (reverse_polynomialStep poly state))

theorem byteStep_injection (poly state byte : BitVec 8) :
    (byteStep poly state byte).reverse =
      crc.polynomialRun poly.reverse true 8 (state.reverse ^^^ byte) := by
  rw [byteStep_eq_reverse_byte, CrcCanonical8.byteStep_injection,
    reverse_polynomialRun, reverse_xor, BitVec.reverse_reverse_eq]
def run (poly initial : BitVec 8) (bytes : List (BitVec 8)) : BitVec 8 :=
  bytes.foldl (byteStep poly) initial

/-- Coherence of the reflected storage table with the canonical polynomial. -/
def TableValid (poly : BitVec 8) (table : BitVec 8 → BitVec 8) : Prop :=
  ∀ byte, table byte = crc.polynomialRun poly.reverse true 8 byte

theorem lookupRun_correct (poly : BitVec 8) (table : BitVec 8 → BitVec 8)
    (ht : TableValid poly table) (state : BitVec 8) (bytes : List (BitVec 8)) :
    CrcCanonical8.lookupRun table state.reverse bytes = (run poly state bytes).reverse := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte bytes ih =>
    simp only [CrcCanonical8.lookupRun, run, List.foldl_cons]
    change CrcCanonical8.lookupRun table (table (state.reverse ^^^ byte)) bytes =
      (run poly (byteStep poly state byte) bytes).reverse
    rw [ht, ← byteStep_injection]
    exact ih _
end CrcReflected8
