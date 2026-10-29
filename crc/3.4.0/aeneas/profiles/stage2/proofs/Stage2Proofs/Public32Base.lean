import Stage2Proofs.InitFinalize
import CrcBody.Funs
open Aeneas Aeneas.Std Result
namespace CrcPublic32
def NonRef32 (a : CrcBody.crc_catalog.Algorithm U32) : Prop :=
  a.width = 32#u8 ∧ a.refin = false

def reverseScalar (value : U32) : U32 := UScalar.mk value.bv.reverse

theorem reverse32 (value : U32) :
    CrcBody.core.num.U32.reverse_bits value = .ok (reverseScalar value) := by
  exact CrcStage2.reverse_bits_u32 value

theorem init_identity (a : CrcBody.crc_catalog.Algorithm U32) (initial : U32)
    (ha : NonRef32 a) : CrcBody.crc32.init a initial = .ok initial := by
  obtain ⟨hw, hri⟩ := ha
  unfold CrcBody.crc32.init
  simp only [hw, hri, Bool.false_eq_true, ↓reduceIte]
  have h : WP.spec (do let i ← 32#u8 - 32#u8; initial <<< i)
      (fun out => out = initial) := by
    step
    step
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    have hz : i.val = 0 := by omega
    simpa only [hz, BitVec.shiftLeft_zero] using out_post1
  obtain ⟨out, hout, rfl⟩ := crc.total_result h
  exact hout

theorem finalize_eq (a : CrcBody.crc_catalog.Algorithm U32) (value : U32)
    (ha : NonRef32 a) :
    CrcBody.crc32.finalize a value =
      .ok ((if a.refout then reverseScalar value else value) ^^^ a.xorout) := by
  obtain ⟨hw, hri⟩ := ha
  cases hro : a.refout with
  | true =>
    unfold CrcBody.crc32.finalize
    simp only [hri, hro, Bool.false_xor, ↓reduceIte, reverse32, bind_ok]
  | false =>
    unfold CrcBody.crc32.finalize
    simp only [hw, hri, hro, Bool.false_xor, Bool.false_eq_true, ↓reduceIte, bind_ok]
    have h : WP.spec (do
        let i ← 32#u8 - 32#u8
        let v ← value >>> i
        .ok (v ^^^ a.xorout)) (fun out => out = value ^^^ a.xorout) := by
      step
      step
      have hz : i.val = 0 := by omega
      have heq : v = value := by
        apply (UScalar.eq_equiv_bv_eq _ _).mpr
        simpa only [hz, BitVec.ushiftRight_zero] using v_post1
      exact congrArg (fun x : U32 => x ^^^ a.xorout) heq
    obtain ⟨out, hout, rfl⟩ := crc.total_result h
    simpa only [Aeneas.Std.bind_assoc] using hout

theorem finalize_total (a : CrcBody.crc_catalog.Algorithm U32) (value : U32)
    (ha : NonRef32 a) :
    ∃ out, CrcBody.crc32.finalize a value = .ok out ∧
      out.bv = (if a.refout then value.bv.reverse else value.bv) ^^^ a.xorout.bv := by
  refine ⟨_, finalize_eq a value ha, ?_⟩
  cases a.refout <;> rfl
end CrcPublic32
