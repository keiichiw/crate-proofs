import CrcBody.Funs
import Stage2Proofs.InitFinalize
open Aeneas Aeneas.Std Result
namespace CrcReflectedPublic32

def Domain (a : CrcBody.crc_catalog.Algorithm U32) : Prop :=
  a.width = 32#u8 ∧ a.refin = true

def reverseScalar (value : U32) : U32 := UScalar.mk value.bv.reverse

@[simp] theorem reverseScalar_bv (value : U32) : (reverseScalar value).bv = value.bv.reverse := rfl

theorem reverse32 (value : U32) :
    CrcBody.core.num.U32.reverse_bits value = .ok (reverseScalar value) := by
  exact CrcStage2.reverse_bits_u32 value

theorem init_eq (a : CrcBody.crc_catalog.Algorithm U32) (initial : U32)
    (ha : Domain a) : CrcBody.crc32.init a initial = .ok (reverseScalar initial) := by
  obtain ⟨hw, hri⟩ := ha
  unfold CrcBody.crc32.init
  simp only [hw, hri, ↓reduceIte, reverse32, bind_ok]
  have h : WP.spec (do let i ← 32#u8 - 32#u8; reverseScalar initial >>> i)
      (fun out => out = reverseScalar initial) := by
    step
    step
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    have hz : i.val = 0 := by omega
    simpa only [hz, BitVec.ushiftRight_zero] using out_post1
  obtain ⟨out, hout, rfl⟩ := crc.total_result h
  exact hout

def finish (a : CrcBody.crc_catalog.Algorithm U32) (state : BitVec 32) : BitVec 32 :=
  (if a.refout then state.reverse else state) ^^^ a.xorout.bv

theorem finalize_eq (a : CrcBody.crc_catalog.Algorithm U32) (value : U32)
    (ha : Domain a) : CrcBody.crc32.finalize a value =
      .ok ((if a.refout then value else reverseScalar value) ^^^ a.xorout) := by
  obtain ⟨hw, hri⟩ := ha
  unfold CrcBody.crc32.finalize
  cases hro : a.refout
  · simp only [hw, hri, hro, Bool.true_xor, Bool.not_false, ↓reduceIte,
      reverse32, bind_ok, Bool.false_eq_true]
    have h : WP.spec (do
        let i ← 32#u8 - 32#u8
        let v ← reverseScalar value >>> i
        .ok (v ^^^ a.xorout))
        (fun out => out = reverseScalar value ^^^ a.xorout) := by
      step
      step
      have hz : i.val = 0 := by omega
      have heq : v = reverseScalar value := by
        apply (UScalar.eq_equiv_bv_eq _ _).mpr
        simpa only [hz, BitVec.ushiftRight_zero] using v_post1
      exact congrArg (fun x : U32 => x ^^^ a.xorout) heq
    obtain ⟨out, hout, rfl⟩ := crc.total_result h
    simpa only [Aeneas.Std.bind_assoc] using hout
  · simp only [hri, hro, Bool.true_xor, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_ok]

 theorem finalize_canonical (a : CrcBody.crc_catalog.Algorithm U32) (value : U32)
    (ha : Domain a) :
    ∃ out, CrcBody.crc32.finalize a value = .ok out ∧ out.bv = finish a value.bv.reverse := by
  refine ⟨(if a.refout then value else reverseScalar value) ^^^ a.xorout, finalize_eq a value ha, ?_⟩
  cases hro : a.refout <;> simp only [finish, hro, Bool.false_eq_true, ↓reduceIte, UScalar.bv_xor,
    reverseScalar, BitVec.reverse_reverse_eq]

end CrcReflectedPublic32
