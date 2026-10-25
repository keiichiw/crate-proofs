import Bytes
open Aeneas Aeneas.Std Result
private theorem bits_sign (x : BitVec 64) (k : Nat) (hk : 0 < k) (hk64 : k ≤ 64) :
    (x <<< (64-k)).sshiftRight (64-k) = (x.setWidth k).signExtend 64 := by
  ext i hi
  simp only [BitVec.getElem_sshiftRight, BitVec.getElem_signExtend, BitVec.getElem_setWidth,
    BitVec.getElem_shiftLeft, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  by_cases h : i < k
  · simp only [h,show 64-k+i < 64 by omega,show ¬64-k+i < 64-k by omega,
      show 64-k+i-(64-k)=i by omega,decide_false,Bool.not_false,Bool.true_and, _root_.dite_true]
    exact (BitVec.getLsbD_eq_getElem hi).symm
  · simp [h,show ¬64-k+i<64 by omega,show ¬63<64-k by omega,hk,
      show 63-(64-k)=k-1 by omega]

private theorem signed_bits (x : BitVec 64) (k : Nat) (hk : 0 < k) (hk64 : k ≤ 64) :
    ((x <<< (64-k)).sshiftRight (64-k)).toInt =
      if x.toNat % 2^k < 2^(k-1) then ((x.toNat % 2^k : Nat) : Int)
      else ((x.toNat % 2^k : Nat) : Int) - ((2^k : Nat) : Int) := by
  rw [bits_sign x k hk hk64, BitVec.toInt_signExtend_of_le hk64]
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_setWidth]
  have hp : 2^k = 2 * 2^(k-1) := by
    conv_lhs => rw [show k=(k-1)+1 by omega, Nat.pow_succ]
    omega
  have heq : 2 * (x.toNat % 2^k) < 2^k ↔ x.toNat % 2^k < 2^(k-1) := by omega
  simp only [heq]
namespace bytes
def signedByteValue (v n : Nat) : Int :=
  if n=0 then 0 else
    let u := v % 2^(8*n)
    if u < 2^(8*n-1) then u else (u : Int) - (2^(8*n) : Nat)

private theorem wp_to_success {α : Type _} {m : Result α} {p : α → Prop}
    (h : WP.spec m p) : ∃ out, m = .ok out ∧ p out := by
  cases m using Result.cases with
  | ret x => exact ⟨x, rfl, (WP.spec_ok x).mp h⟩
  | vis effect k => exact False.elim ((WP.spec_vis effect k).mp h)
  | div => exact False.elim (WP.spec_div.mp h)

theorem sign_extend_spec (v : U64) (n : Usize) (hn : n.val ≤ 8) :
    ∃ out, buf.buf_impl.sign_extend v n = .ok out ∧ out.val = signedByteValue v.val n.val := by
  apply wp_to_success
  unfold buf.buf_impl.sign_extend
  split
  · rename_i hz
    simp_all [signedByteValue]
  · rename_i hnz
    step
    step
    step
    step
    step
    have hn0 : 0 < n.val := by scalar_tac
    have hs : shift.val = 64 - 8*n.val := by omega
    have hk0 : 0 < 8*n.val := by omega
    have hk64 : 8*n.val ≤ 64 := by omega
    have hm := signed_bits v.bv (8*n.val) hk0 hk64
    have hcast : i2.bv = i1.bv := by rw [i2_post]; rfl
    simp only [IScalar.val] at ⊢
    simp only [out_post1,hcast,i1_post1,hs]
    have hn0bv : n.bv.toNat ≠ 0 := by simpa only [UScalar.val] using (Nat.ne_of_gt hn0)
    simpa only [signedByteValue,UScalar.val,ite_eq_right hn0bv] using hm
end bytes
