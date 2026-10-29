import Stage2Proofs.ByteMathWide
import Stage2Proofs.ReflectMath8
namespace CrcReflectedWide

theorem reverse_xor {N : Nat} (a b : BitVec N) :
    (a ^^^ b).reverse = a.reverse ^^^ b.reverse := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_reverse, BitVec.getLsbD_xor,
    BitVec.getMsbD_eq_getLsbD, hi, decide_true, Bool.true_and]

theorem reverse_shiftLeft_one {N : Nat} (a : BitVec N) :
    (a <<< 1).reverse = a.reverse >>> 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    hi, decide_true, Bool.true_and]
  by_cases h : i+1 < N
  · have hb : 1 ≤ N-1-i := by omega
    have he : N-1-i-1 = N-1-(i+1) := by omega
    have ht : N-1-i < N := by omega
    have hb' : ¬ N-1-i < 1 := by omega
    simp only [Nat.add_comm, h, ht, hb', he, decide_true, decide_false, Bool.not_false, Bool.true_and]
  · have hz : N-1-i = 0 := by omega
    simp [h, hz, Nat.add_comm]

theorem reverse_polynomialStep {N : Nat} (hN : 0 < N) (poly state : BitVec N) :
    (crc.polynomialStep poly state false).reverse =
      crc.polynomialStep poly.reverse state.reverse true := by
  unfold crc.polynomialStep
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [reverse_xor, reverse_shiftLeft_one]
  have hb : state.reverse.getLsbD 0 = state.getLsbD (N-1) := by
    simp only [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD,
      hN, decide_true, Bool.true_and, Nat.sub_zero]
  rw [hb]
  have hz : (0 : BitVec N).reverse = 0 := BitVec.reverse_eq_zero_iff.mpr rfl
  cases h : state.getLsbD (N-1)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact congrArg (fun x : BitVec N => (state.reverse >>> 1) ^^^ x) hz
  · rfl

theorem reverse_polynomialRun {N : Nat} (hN : 0 < N) (poly state : BitVec N) (n : Nat) :
    (crc.polynomialRun poly false n state).reverse =
      crc.polynomialRun poly.reverse true n state.reverse := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
    simp only [crc.polynomialRun]
    exact (ih _).trans (congrArg (crc.polynomialRun poly.reverse true n)
      (reverse_polynomialStep hN poly state))

def byteStep {N : Nat} (poly state : BitVec N) (byte : BitVec 8) : BitVec N :=
  (CrcReflected8.byteBits byte).foldl (CrcCanonicalWide.inputStep poly) state

def run {N : Nat} (poly initial : BitVec N) (bytes : List (BitVec 8)) : BitVec N :=
  bytes.foldl (byteStep poly) initial

theorem byteStep_eq_reverse_byte {N : Nat} (poly state : BitVec N) (byte : BitVec 8) :
    byteStep poly state byte = CrcCanonicalWide.byteStep poly state byte.reverse := by
  simp only [byteStep, CrcReflected8.byteBits, CrcCanonicalWide.byteStep, CrcCanonical8.byteBits,
    BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD]
  rfl

theorem reverse_encodeByte {N : Nat} (hN : 8 ≤ N) (byte : BitVec 8) :
    (CrcCanonicalWide.encodeByte N byte.reverse).reverse = byte.setWidth N := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [CrcCanonicalWide.encodeByte, BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    hi, decide_true, Bool.true_and]
  by_cases hb : i < 8
  · have hshift : N-8 ≤ N-1-i := by omega
    have hindex : N-1-i-(N-8) = 7-i := by omega
    have hindexN : 7-i < N := by omega
    have hindex8 : 7-i < 8 := by omega
    have hinverse : 8-1-(7-i) = i := by omega
    have ht : N-1-i < N := by omega
    have hb' : ¬ N-1-i < N-8 := by omega
    simp only [hindex, hindexN, hindex8, hinverse, ht, hb', decide_true, decide_false,
      Bool.not_false, Bool.true_and]
  · have hshift : ¬ N-8 ≤ N-1-i := by omega
    have ht : N-1-i < N-8 := by omega
    have hz : byte.getLsbD i = false := BitVec.getLsbD_of_ge byte i (by omega)
    simp [ht, hz]
theorem byteStep_injection {N : Nat} (hN : 8 ≤ N) (poly state : BitVec N) (byte : BitVec 8) :
    (byteStep poly state byte).reverse =
      crc.polynomialRun poly.reverse true 8 (state.reverse ^^^ byte.setWidth N) := by
  rw [byteStep_eq_reverse_byte, CrcCanonicalWide.byteStep_injection hN,
    reverse_polynomialRun (by omega), reverse_xor, reverse_encodeByte hN]
theorem polynomialStep_xor {N : Nat} (poly a b : BitVec N) :
    crc.polynomialStep poly (a ^^^ b) true =
      crc.polynomialStep poly a true ^^^ crc.polynomialStep poly b true := by
  unfold crc.polynomialStep
  simp only [↓reduceIte, BitVec.getLsbD_xor, BitVec.ushiftRight_xor_distrib]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor]
  cases ha : a.getLsbD 0 <;> cases hb : b.getLsbD 0 <;>
    simp [Bool.xor_comm, Bool.xor_left_comm]

theorem polynomialRun_xor {N : Nat} (poly a b : BitVec N) (n : Nat) :
    crc.polynomialRun poly true n (a ^^^ b) =
      crc.polynomialRun poly true n a ^^^ crc.polynomialRun poly true n b := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [crc.polynomialRun, polynomialStep_xor]
    exact ih _ _

theorem polynomialRun_no_feedback {N : Nat} (poly state : BitVec N) (n : Nat)
    (h : ∀ k, k < n → (state >>> k).getLsbD 0 = false) :
    crc.polynomialRun poly true n state = state >>> n := by
  induction n generalizing state with
  | zero => simp [crc.polynomialRun]
  | succ n ih =>
    have h0 : state.getLsbD 0 = false := by simpa using h 0 (by omega)
    have hs : crc.polynomialStep poly state true = state >>> 1 := by
      simp [crc.polynomialStep, h0]
    simp only [crc.polynomialRun, hs]
    have hn : ∀ k, k < n → ((state >>> 1) >>> k).getLsbD 0 = false := by
      intro k hk
      simpa [← BitVec.shiftRight_add, Nat.add_comm] using h (k+1) (by omega)
    exact (ih (state >>> 1) hn).trans (by rw [← BitVec.shiftRight_add]; congr 1; omega)

def lowByte {N : Nat} (state : BitVec N) : BitVec N := (state.setWidth 8).setWidth N

def highBytes {N : Nat} (state : BitVec N) : BitVec N := (state >>> 8) <<< 8

theorem split_state {N : Nat} (state : BitVec N) : state = highBytes state ^^^ lowByte state := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlo : i < 8
  · simp [lowByte, highBytes, hi, hlo]
  · have hidx : i-8+8 = i := by omega
    simp [lowByte, highBytes, hi, hlo, show 8 ≤ i by omega]

theorem highBytes_run8 {N : Nat} (hN : 8 ≤ N) (poly state : BitVec N) :
    crc.polynomialRun poly true 8 (highBytes state) = state >>> 8 := by
  have h : ∀ k, k < 8 → ((highBytes state) >>> k).getLsbD 0 = false := by
    intro k hk
    simp [highBytes, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, hk]
  have hr := polynomialRun_no_feedback poly (highBytes state) 8 h
  apply hr.trans
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [highBytes, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  have hi8 : ¬ 8+i < 8 := by omega
  have hsub : 8+i-8 = i := by omega
  simp only [hi8, hsub, hi, decide_false, decide_true, Bool.not_false, Bool.true_and, Bool.and_true]
  by_cases hbound : 8+i < N
  · simp only [hbound, decide_true, Bool.true_and]
  · simp only [hbound, decide_false, Bool.false_and]
    exact (BitVec.getLsbD_of_ge state (8+i) (by omega)).symm

theorem lowByte_mask {N : Nat} (state : BitVec N) : lowByte state = state &&& 255 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [lowByte, BitVec.getLsbD_setWidth, BitVec.getLsbD_and]
  by_cases hb : i < 8
  · have hm : (255 : BitVec N).getLsbD i = true := by
      change (BitVec.ofNat N 255).getLsbD i = _
      simp only [BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
      have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    simp only [hi, hb, hm, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false]
  · have hm : (255 : BitVec N).getLsbD i = false := by
      change (BitVec.ofNat N 255).getLsbD i = _
      simp only [BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
      apply Nat.testBit_lt_two_pow
      have hpow : 2^8 ≤ (2:Nat)^i := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (by omega : 8 ≤ i)
      omega
    simp only [hi, hb, hm, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false]

theorem polynomialRun_split8 {N : Nat} (hN : 8 ≤ N) (poly state : BitVec N) :
    crc.polynomialRun poly true 8 state = (state >>> 8) ^^^
      crc.polynomialRun poly true 8 (state &&& 255) := by
  conv_lhs => rw [split_state state]
  rw [polynomialRun_xor, highBytes_run8 hN, lowByte_mask]
end CrcReflectedWide
