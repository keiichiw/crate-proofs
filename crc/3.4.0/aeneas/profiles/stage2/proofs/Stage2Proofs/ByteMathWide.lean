import Stage2Proofs.ByteMath
namespace CrcCanonicalWide

def inputStep {N : Nat} (poly state : BitVec N) (bit : Bool) : BitVec N :=
  (state <<< 1) ^^^ (if state.getLsbD (N-1) != bit then poly else 0)

def byteStep {N : Nat} (poly state : BitVec N) (byte : BitVec 8) : BitVec N :=
  (CrcCanonical8.byteBits byte).foldl (inputStep poly) state

def run {N : Nat} (poly state : BitVec N) (bytes : List (BitVec 8)) : BitVec N :=
  bytes.foldl (byteStep poly) state

def encodeByte (N : Nat) (byte : BitVec 8) : BitVec N := byte.setWidth N <<< (N-8)

def feed {N : Nat} (poly : BitVec N) : Nat → BitVec N → BitVec N → BitVec N
  | 0, state, _ => state
  | n+1, state, message => feed poly n (inputStep poly state (message.getLsbD (N-1))) (message <<< 1)

def shiftMessage {N : Nat} : Nat → BitVec N → BitVec N
  | 0, message => message
  | n+1, message => shiftMessage n (message <<< 1)

theorem injection_step {N : Nat} (poly state message : BitVec N) :
    inputStep poly state (message.getLsbD (N-1)) ^^^ (message <<< 1) =
      crc.polynomialStep poly (state ^^^ message) false := by
  unfold inputStep crc.polynomialStep
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_xor]
  rw [BitVec.shiftLeft_xor_distrib]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor]
  cases hs : state.getLsbD (N-1) <;> cases hb : message.getLsbD (N-1) <;>
    simp [Bool.xor_comm]

theorem feed_injection {N : Nat} (poly state message : BitVec N) (n : Nat) :
    feed poly n state message =
      crc.polynomialRun poly false n (state ^^^ message) ^^^ shiftMessage n message := by
  induction n generalizing state message with
  | zero =>
    apply BitVec.eq_of_getLsbD_eq
    intro i
    simp [feed, crc.polynomialRun, shiftMessage]
  | succ n ih =>
    simp only [feed, shiftMessage, crc.polynomialRun]
    rw [ih, injection_step]

theorem shiftMessage_eq {N : Nat} (n : Nat) (message : BitVec N) :
    shiftMessage n message = message <<< n := by
  induction n generalizing message with
  | zero => simp [shiftMessage]
  | succ n ih =>
    simp only [shiftMessage, ih, ← BitVec.shiftLeft_add]
    congr 1
    omega

theorem encodeByte_bit {N k : Nat} (hN : 8 ≤ N) (hk : k < 8) (byte : BitVec 8) :
    ((encodeByte N byte) <<< k).getLsbD (N-1) = byte.getLsbD (7-k) := by
  have htop : N-1 < N := by omega
  have hbound : N-8+k ≤ N-1 := by omega
  have heq : N-1-(N-8+k) = 7-k := by omega
  have hbit : 7-k < 8 := by omega
  simp [encodeByte, ← BitVec.shiftLeft_add, htop, hbound, heq, hbit]

theorem byteStep_injection {N : Nat} (hN : 8 ≤ N) (poly state : BitVec N) (byte : BitVec 8) :
    byteStep poly state byte =
      crc.polynomialRun poly false 8 (state ^^^ encodeByte N byte) := by
  have h := feed_injection poly state (encodeByte N byte) 8
  have hf : feed poly 8 state (encodeByte N byte) = byteStep poly state byte := by
    simp only [feed, byteStep, CrcCanonical8.byteBits, List.foldl_cons, List.foldl_nil,
      ← BitVec.shiftLeft_add]
    simp only [show (encodeByte N byte).getLsbD (N-1) = byte.getLsbD 7 from
      (by simpa using encodeByte_bit hN (by decide : 0 < 8) byte)]
    simp only [encodeByte_bit hN (by decide : 1 < 8),
      encodeByte_bit hN (by decide : 2 < 8), encodeByte_bit hN (by decide : 3 < 8),
      encodeByte_bit hN (by decide : 4 < 8), encodeByte_bit hN (by decide : 5 < 8),
      encodeByte_bit hN (by decide : 6 < 8), encodeByte_bit hN (by decide : 7 < 8)]
  have hz : shiftMessage 8 (encodeByte N byte) = 0 := by
    rw [shiftMessage_eq]
    simp [encodeByte, ← BitVec.shiftLeft_add, Nat.sub_add_cancel hN]
  rw [hf, hz] at h
  exact h.trans (by apply BitVec.eq_of_getLsbD_eq; intro i hi; simp)

theorem polynomialStep_xor {N : Nat} (poly a b : BitVec N) :
    crc.polynomialStep poly (a ^^^ b) false =
      crc.polynomialStep poly a false ^^^ crc.polynomialStep poly b false := by
  unfold crc.polynomialStep
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_xor,
    BitVec.shiftLeft_xor_distrib]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor]
  cases ha : a.getLsbD (N-1) <;> cases hb : b.getLsbD (N-1) <;>
    simp [Bool.xor_comm, Bool.xor_left_comm]

theorem polynomialRun_xor {N : Nat} (poly a b : BitVec N) (n : Nat) :
    crc.polynomialRun poly false n (a ^^^ b) =
      crc.polynomialRun poly false n a ^^^ crc.polynomialRun poly false n b := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [crc.polynomialRun, polynomialStep_xor]
    exact ih _ _

theorem polynomialRun_no_feedback {N : Nat} (poly state : BitVec N) (n : Nat)
    (h : ∀ k, k < n → (state <<< k).getLsbD (N-1) = false) :
    crc.polynomialRun poly false n state = state <<< n := by
  induction n generalizing state with
  | zero => simp [crc.polynomialRun]
  | succ n ih =>
    have h0 : state.getLsbD (N-1) = false := by simpa using h 0 (by omega)
    have hs : crc.polynomialStep poly state false = state <<< 1 := by
      simp [crc.polynomialStep, h0]
    simp only [crc.polynomialRun, hs]
    have hn : ∀ k, k < n → ((state <<< 1) <<< k).getLsbD (N-1) = false := by
      intro k hk
      simpa [← BitVec.shiftLeft_add, Nat.add_comm] using h (k+1) (by omega)
    exact (ih (state <<< 1) hn).trans (by rw [← BitVec.shiftLeft_add]; congr 1; omega)

def lowPart {N : Nat} (state : BitVec N) : BitVec N := (state.setWidth (N-8)).setWidth N

def highPart {N : Nat} (state : BitVec N) : BitVec N := (state >>> (N-8)) <<< (N-8)

theorem split_state {N : Nat} (state : BitVec N) : state = lowPart state ^^^ highPart state := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlo : i < N-8
  · simp [lowPart, highPart, hi, hlo]
  · have hidx : i-(N-8)+(N-8) = i := by omega
    simp [lowPart, highPart, hi, hlo, show N-8 ≤ i by omega]

theorem lowPart_run8 {N : Nat} (hN : 8 ≤ N) (poly state : BitVec N) :
    crc.polynomialRun poly false 8 (lowPart state) = state <<< 8 := by
  have h : ∀ k, k < 8 → ((lowPart state) <<< k).getLsbD (N-1) = false := by
    intro k hk
    have hb : ¬N-1-k < N-8 := by omega
    simp [lowPart, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hb]
  have hr := polynomialRun_no_feedback poly (lowPart state) 8 h
  have hz : highPart state <<< 8 = 0 := by
    simp [highPart, ← BitVec.shiftLeft_add, Nat.sub_add_cancel hN]
  refine hr.trans ?_
  have hs := congrArg (fun x : BitVec N => x <<< 8) (split_state state)
  rw [BitVec.shiftLeft_xor_distrib, hz] at hs
  exact (hs.trans (by apply BitVec.eq_of_getLsbD_eq; intro i hi; simp)).symm

theorem polynomialRun_split8 {N : Nat} (hN : 8 ≤ N) (poly state : BitVec N) :
    crc.polynomialRun poly false 8 state = (state <<< 8) ^^^
      crc.polynomialRun poly false 8 ((state >>> (N-8)) <<< (N-8)) := by
  conv_lhs => rw [split_state state]
  rw [polynomialRun_xor, lowPart_run8 hN]
  rfl
end CrcCanonicalWide
