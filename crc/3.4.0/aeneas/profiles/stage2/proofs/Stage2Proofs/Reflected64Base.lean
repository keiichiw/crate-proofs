import CrcBody.Funs
import Stage2Proofs.InitFinalize
open Aeneas Aeneas.Std Result
namespace CrcReflectedPublic64

def Domain (a : CrcBody.crc_catalog.Algorithm U64) : Prop :=
  a.width = 64#u8 ∧ a.refin = true

def reverseScalar (value : U64) : U64 := UScalar.mk value.bv.reverse

@[simp] theorem reverseScalar_bv (value : U64) : (reverseScalar value).bv = value.bv.reverse := rfl

theorem reverse64 (value : U64) :
    CrcBody.core.num.U64.reverse_bits value = .ok (reverseScalar value) := by
  exact CrcStage2.reverse_bits_u64 value

theorem init_eq (a : CrcBody.crc_catalog.Algorithm U64) (initial : U64)
    (ha : Domain a) : CrcBody.crc64.init a initial = .ok (reverseScalar initial) := by
  obtain ⟨hw, hri⟩ := ha
  unfold CrcBody.crc64.init
  simp only [hw, hri, ↓reduceIte, reverse64, bind_ok]
  have h : WP.spec (do let i ← 64#u8 - 64#u8; reverseScalar initial >>> i)
      (fun out => out = reverseScalar initial) := by
    step
    step
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    have hz : i.val = 0 := by omega
    simpa only [hz, BitVec.ushiftRight_zero] using out_post1
  obtain ⟨out, hout, rfl⟩ := crc.total_result h
  exact hout

def finish (a : CrcBody.crc_catalog.Algorithm U64) (state : BitVec 64) : BitVec 64 :=
  (if a.refout then state.reverse else state) ^^^ a.xorout.bv

theorem finalize_eq (a : CrcBody.crc_catalog.Algorithm U64) (value : U64)
    (ha : Domain a) : CrcBody.crc64.finalize a value =
      .ok ((if a.refout then value else reverseScalar value) ^^^ a.xorout) := by
  obtain ⟨hw, hri⟩ := ha
  unfold CrcBody.crc64.finalize
  cases hro : a.refout
  · simp only [hw, hri, hro, Bool.true_xor, Bool.not_false, ↓reduceIte,
      reverse64, bind_ok, Bool.false_eq_true]
    have h : WP.spec (do
        let i ← 64#u8 - 64#u8
        let v ← reverseScalar value >>> i
        .ok (v ^^^ a.xorout))
        (fun out => out = reverseScalar value ^^^ a.xorout) := by
      step
      step
      have hz : i.val = 0 := by omega
      have heq : v = reverseScalar value := by
        apply (UScalar.eq_equiv_bv_eq _ _).mpr
        simpa only [hz, BitVec.ushiftRight_zero] using v_post1
      exact congrArg (fun x : U64 => x ^^^ a.xorout) heq
    obtain ⟨out, hout, rfl⟩ := crc.total_result h
    simpa only [Aeneas.Std.bind_assoc] using hout
  · simp only [hri, hro, Bool.true_xor, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_ok]

 theorem finalize_canonical (a : CrcBody.crc_catalog.Algorithm U64) (value : U64)
    (ha : Domain a) :
    ∃ out, CrcBody.crc64.finalize a value = .ok out ∧ out.bv = finish a value.bv.reverse := by
  refine ⟨(if a.refout then value else reverseScalar value) ^^^ a.xorout, finalize_eq a value ha, ?_⟩
  cases hro : a.refout <;> simp only [finish, hro, Bool.false_eq_true, ↓reduceIte, UScalar.bv_xor,
    reverseScalar, BitVec.reverse_reverse_eq]

end CrcReflectedPublic64
