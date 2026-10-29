import Stage2Proofs.InitFinalize
import CrcBody.Funs
open Aeneas Aeneas.Std Result
namespace CrcPublic128
def NonRef128 (a : CrcBody.crc_catalog.Algorithm U128) : Prop :=
  a.width = 128#u8 ∧ a.refin = false

def reverseScalar (value : U128) : U128 := UScalar.mk value.bv.reverse

theorem reverse128 (value : U128) :
    CrcBody.core.num.U128.reverse_bits value = .ok (reverseScalar value) := by
  exact CrcStage2.reverse_bits_u128 value

theorem init_identity (a : CrcBody.crc_catalog.Algorithm U128) (initial : U128)
    (ha : NonRef128 a) : CrcBody.crc128.init a initial = .ok initial := by
  obtain ⟨hw, hri⟩ := ha
  unfold CrcBody.crc128.init
  simp only [hw, hri, Bool.false_eq_true, ↓reduceIte]
  have h : WP.spec (do let i ← 128#u8 - 128#u8; initial <<< i)
      (fun out => out = initial) := by
    step
    step
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    have hz : i.val = 0 := by omega
    simpa only [hz, BitVec.shiftLeft_zero] using out_post1
  obtain ⟨out, hout, rfl⟩ := crc.total_result h
  exact hout

theorem finalize_eq (a : CrcBody.crc_catalog.Algorithm U128) (value : U128)
    (ha : NonRef128 a) :
    CrcBody.crc128.finalize a value =
      .ok ((if a.refout then reverseScalar value else value) ^^^ a.xorout) := by
  obtain ⟨hw, hri⟩ := ha
  cases hro : a.refout with
  | true =>
    unfold CrcBody.crc128.finalize
    simp only [hri, hro, Bool.false_xor, ↓reduceIte, reverse128, bind_ok]
  | false =>
    unfold CrcBody.crc128.finalize
    simp only [hw, hri, hro, Bool.false_xor, Bool.false_eq_true, ↓reduceIte, bind_ok]
    have h : WP.spec (do
        let i ← 128#u8 - 128#u8
        let v ← value >>> i
        .ok (v ^^^ a.xorout)) (fun out => out = value ^^^ a.xorout) := by
      step
      step
      have hz : i.val = 0 := by omega
      have heq : v = value := by
        apply (UScalar.eq_equiv_bv_eq _ _).mpr
        simpa only [hz, BitVec.ushiftRight_zero] using v_post1
      exact congrArg (fun x : U128 => x ^^^ a.xorout) heq
    obtain ⟨out, hout, rfl⟩ := crc.total_result h
    simpa only [Aeneas.Std.bind_assoc] using hout

theorem finalize_total (a : CrcBody.crc_catalog.Algorithm U128) (value : U128)
    (ha : NonRef128 a) :
    ∃ out, CrcBody.crc128.finalize a value = .ok out ∧
      out.bv = (if a.refout then value.bv.reverse else value.bv) ^^^ a.xorout.bv := by
  refine ⟨_, finalize_eq a value ha, ?_⟩
  cases a.refout <;> rfl
end CrcPublic128
