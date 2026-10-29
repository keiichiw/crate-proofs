import CrcProofs.EightPolynomial
namespace CrcCanonical8

def inputStep (poly state : BitVec 8) (bit : Bool) : BitVec 8 :=
  (state <<< 1) ^^^ (if state.getLsbD 7 != bit then poly else 0)

def byteBits (byte : BitVec 8) : List Bool :=
  [byte.getLsbD 7, byte.getLsbD 6, byte.getLsbD 5, byte.getLsbD 4,
   byte.getLsbD 3, byte.getLsbD 2, byte.getLsbD 1, byte.getLsbD 0]

def byteStep (poly state byte : BitVec 8) : BitVec 8 :=
  (byteBits byte).foldl (inputStep poly) state

def run (poly initial : BitVec 8) (bytes : List (BitVec 8)) : BitVec 8 :=
  bytes.foldl (byteStep poly) initial

def feed (poly : BitVec 8) : Nat → BitVec 8 → BitVec 8 → BitVec 8
  | 0, state, _ => state
  | n+1, state, byte => feed poly n (inputStep poly state (byte.getLsbD 7)) (byte <<< 1)

def shiftByte : Nat → BitVec 8 → BitVec 8
  | 0, byte => byte
  | n+1, byte => shiftByte n (byte <<< 1)

theorem injection_step (poly state byte : BitVec 8) :
    inputStep poly state (byte.getLsbD 7) ^^^ (byte <<< 1) =
      crc.polynomialStep poly (state ^^^ byte) false := by
  unfold inputStep crc.polynomialStep
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_xor]
  rw [BitVec.shiftLeft_xor_distrib]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor]
  cases hs : state.getLsbD 7 <;> cases hb : byte.getLsbD 7 <;>
    simp [Bool.xor_comm]

theorem feed_injection (poly state byte : BitVec 8) (n : Nat) :
    feed poly n state byte =
      crc.polynomialRun poly false n (state ^^^ byte) ^^^ shiftByte n byte := by
  induction n generalizing state byte with
  | zero =>
    apply BitVec.eq_of_getLsbD_eq
    intro i
    simp [feed, crc.polynomialRun, shiftByte]
  | succ n ih =>
    simp only [feed, shiftByte, crc.polynomialRun]
    rw [ih, injection_step]

theorem byteStep_injection (poly state byte : BitVec 8) :
    byteStep poly state byte = crc.polynomialRun poly false 8 (state ^^^ byte) := by
  have h := feed_injection poly state byte 8
  have hf : feed poly 8 state byte = byteStep poly state byte := by
    simp [feed, byteStep, byteBits, List.foldl]
  have hz : shiftByte 8 byte = 0 := by
    simp [shiftByte, ← BitVec.shiftLeft_add]

  rw [hf, hz] at h
  exact h.trans (by apply BitVec.eq_of_getLsbD_eq; intro i hi; simp)

def TableValid (poly : BitVec 8) (table : BitVec 8 → BitVec 8) : Prop :=
  ∀ byte, table byte = byteStep poly 0 byte

theorem lookup_byteStep (poly : BitVec 8) (table : BitVec 8 → BitVec 8)
    (ht : TableValid poly table) (state byte : BitVec 8) :
    table (state ^^^ byte) = byteStep poly state byte := by
  rw [ht, byteStep_injection, byteStep_injection]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp

def lookupRun (table : BitVec 8 → BitVec 8) (initial : BitVec 8)
    (bytes : List (BitVec 8)) : BitVec 8 :=
  bytes.foldl (fun state byte => table (state ^^^ byte)) initial

theorem lookupRun_correct (poly : BitVec 8) (table : BitVec 8 → BitVec 8)
    (ht : TableValid poly table) (state : BitVec 8) (bytes : List (BitVec 8)) :
    lookupRun table state bytes = run poly state bytes := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte bytes ih =>
    simp only [lookupRun, run, List.foldl_cons]
    change lookupRun table (table (state ^^^ byte)) bytes = run poly (byteStep poly state byte) bytes
    rw [lookup_byteStep poly table ht]
    exact ih _

theorem utility_byteStep (poly byte : Aeneas.Std.U8) :
    ∃ out, crc.util.crc8 poly false byte = .ok out ∧
      out.bv = byteStep poly.bv 0 byte.bv := by
  obtain ⟨out, hout, hv⟩ := crc.crc8_polynomial_spec poly byte false
  refine ⟨out, hout, hv.trans ?_⟩
  rw [byteStep_injection]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp

end CrcCanonical8
