import Stage2Proofs.WidthEncoding
import Stage2Proofs.FullWidthSpec
import Stage2Proofs.InitFinalize
import CrcBody.Funs
open Aeneas Aeneas.Std Result
namespace CrcWidthEndpoints
open CrcWidthEncoding

def storedEncode {w : Nat} (N : Nat) (refin : Bool) (state : BitVec w) : BitVec N :=
  if refin then (encode N state).reverse else encode N state

theorem reverse_shiftLeft {N : Nat} (a : BitVec N) (k : Nat) :
    (a <<< k).reverse = a.reverse >>> k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : a <<< (k+1) = (a <<< k) <<< 1 := (BitVec.shiftLeft_add a k 1)
    rw [he, CrcReflectedWide.reverse_shiftLeft_one, ih, ← BitVec.shiftRight_add]

theorem reverse_encode {w N : Nat} (hN : w ≤ N) (state : BitVec w) :
    (encode N state).reverse = state.reverse.setWidth N := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [encode, BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  by_cases hb : i < w
  · have hindex : N-1-i-(N-w) = w-1-i := by omega
    have hindexN : w-1-i < N := by omega
    have hindexw : w-1-i < w := by omega
    have hinverse : w-1-(w-1-i) = i := by omega
    have ht : N-1-i < N := by omega
    have hs : ¬ N-1-i < N-w := by omega
    simp only [hindex, hindexN, hindexw, hinverse, ht, hs, hb,
      decide_true, decide_false, Bool.not_false, Bool.true_and]
  · have ht : N-1-i < N-w := by omega
    simp only [ht, hb, decide_false, decide_true, Bool.not_true,
      Bool.and_false, Bool.false_and]

theorem encode_shiftRight {w N : Nat} (hN : w ≤ N) (state : BitVec w) :
    encode N state >>> (N-w) = state.setWidth N := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [encode, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  have hsub : N-w+i-(N-w) = i := by omega
  have hs : ¬N-w+i < N-w := by omega
  by_cases hb : i < w
  · have htop : N-w+i < N := by omega
    simp only [hsub, hs, htop, hb, hi, decide_true, decide_false, Bool.not_false, Bool.true_and]
  · have htop : ¬ N-w+i < N := by omega
    have hz : state.getLsbD i = false := BitVec.getLsbD_of_ge state i (by omega)
    simp only [hsub, hs, htop, hb, hz, decide_true, decide_false,
      Bool.not_false, Bool.false_and]

theorem encode_low {w N : Nat} (hN : w ≤ N) (value : BitVec N) :
    encode N (value.setWidth w) = value <<< (N-w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [encode, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases hb : i < N-w
  · simp only [hb, decide_true, Bool.not_true, Bool.and_false, Bool.false_and]
  · have hbit : i-(N-w) < w := by omega
    have hbitN : i-(N-w) < N := by omega
    simp only [hb, hbit, hbitN, decide_true, decide_false, Bool.not_false, Bool.true_and]

theorem rawInit_encoded {w N : Nat} (hN : w ≤ N) (refin : Bool) (value : BitVec N) :
    CrcStage2.rawInit w refin value = storedEncode N refin (value.setWidth w) := by
  cases refin
  · exact (encode_low hN value).symm
  · exact ((congrArg BitVec.reverse (encode_low hN value)).trans (reverse_shiftLeft value (N-w))).symm

theorem rawFinalize_encoded {w N : Nat} (hN : w ≤ N) (refin refout : Bool)
    (xorout state : BitVec w) :
    CrcStage2.rawFinalize w refin refout (xorout.setWidth N) (storedEncode N refin state) =
      ((if refout then state.reverse else state) ^^^ xorout).setWidth N := by
  cases refin <;> cases refout <;>
    simp only [CrcStage2.rawFinalize, storedEncode, Bool.false_xor, Bool.true_xor,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, BitVec.reverse_reverse_eq]
  all_goals first
    | exact (congrArg (fun x : BitVec N => x ^^^ xorout.setWidth N) (encode_shiftRight hN state)).trans BitVec.setWidth_xor.symm
    | exact (congrArg (fun x : BitVec N => x ^^^ xorout.setWidth N) (reverse_encode hN state)).trans BitVec.setWidth_xor.symm

theorem encode_reflected_byteStep {w N : Nat} (hw : 1 ≤ w) (hN : w ≤ N)
    (poly state : BitVec w) (byte : BitVec 8) :
    encode N (CrcReflectedWide.byteStep poly state byte) =
      CrcReflectedWide.byteStep (encode N poly) (encode N state) byte :=
  encode_fold_bits hw hN poly state (CrcReflected8.byteBits byte)

theorem encode_reflected_run {w N : Nat} (hw : 1 ≤ w) (hN : w ≤ N)
    (poly state : BitVec w) (bytes : List (BitVec 8)) :
    encode N (CrcReflectedWide.run poly state bytes) =
      CrcReflectedWide.run (encode N poly) (encode N state) bytes := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte bytes ih =>
    simp only [CrcReflectedWide.run, List.foldl_cons] at *
    rw [ih, encode_reflected_byteStep hw hN]

theorem encode_run {w N : Nat} (hw : 1 ≤ w) (hN : w ≤ N)
    (refin : Bool) (poly state : BitVec w) (bytes : List (BitVec 8)) :
    encode N (CrcFullWidthSpec.run refin poly state bytes) =
      CrcFullWidthSpec.run refin (encode N poly) (encode N state) bytes := by
  cases refin
  · exact CrcWidthEncoding.encode_run hw hN poly state bytes
  · exact encode_reflected_run hw hN poly state bytes
def algorithmToStage {T : Type} (a : CrcBody.crc_catalog.Algorithm T) :
    CrcStage2.crc_catalog.Algorithm T :=
  ⟨a.width,a.poly,a.init,a.refin,a.refout,a.xorout,a.check,a.residue⟩

theorem init8_encoded (a : CrcBody.crc_catalog.Algorithm U8) (initial : U8)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 8) :
    ∃ out, CrcBody.crc8.init a initial = .ok out ∧
      out.bv = storedEncode 8 a.refin (initial.bv.setWidth a.width.val) := by
  obtain ⟨out,ho,hv⟩ := CrcStage2.init8_spec (algorithmToStage a) initial hw
  refine ⟨out, ho, ?_⟩
  exact hv.trans (rawInit_encoded hw.2 a.refin initial.bv)

theorem finalize8_encoded (a : CrcBody.crc_catalog.Algorithm U8)
    (value : U8) (xorout state : BitVec a.width.val)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 8)
    (hxor : a.xorout.bv = xorout.setWidth 8)
    (hstate : value.bv = storedEncode 8 a.refin state) :
    ∃ out, CrcBody.crc8.finalize a value = .ok out ∧
      out.bv = ((if a.refout then state.reverse else state) ^^^ xorout).setWidth 8 := by
  obtain ⟨out,ho,hv⟩ := CrcStage2.finalize8_spec (algorithmToStage a) value hw
  refine ⟨out,ho,?_⟩
  change out.bv = CrcStage2.rawFinalize a.width.val a.refin a.refout a.xorout.bv value.bv at hv
  rw [hxor,hstate] at hv
  exact hv.trans (rawFinalize_encoded hw.2 a.refin a.refout xorout state)

theorem init16_encoded (a : CrcBody.crc_catalog.Algorithm U16) (initial : U16)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 16) :
    ∃ out, CrcBody.crc16.init a initial = .ok out ∧
      out.bv = storedEncode 16 a.refin (initial.bv.setWidth a.width.val) := by
  obtain ⟨out,ho,hv⟩ := CrcStage2.init16_spec (algorithmToStage a) initial hw
  refine ⟨out, ho, ?_⟩
  exact hv.trans (rawInit_encoded hw.2 a.refin initial.bv)

theorem finalize16_encoded (a : CrcBody.crc_catalog.Algorithm U16)
    (value : U16) (xorout state : BitVec a.width.val)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 16)
    (hxor : a.xorout.bv = xorout.setWidth 16)
    (hstate : value.bv = storedEncode 16 a.refin state) :
    ∃ out, CrcBody.crc16.finalize a value = .ok out ∧
      out.bv = ((if a.refout then state.reverse else state) ^^^ xorout).setWidth 16 := by
  obtain ⟨out,ho,hv⟩ := CrcStage2.finalize16_spec (algorithmToStage a) value hw
  refine ⟨out,ho,?_⟩
  change out.bv = CrcStage2.rawFinalize a.width.val a.refin a.refout a.xorout.bv value.bv at hv
  rw [hxor,hstate] at hv
  exact hv.trans (rawFinalize_encoded hw.2 a.refin a.refout xorout state)

theorem init32_encoded (a : CrcBody.crc_catalog.Algorithm U32) (initial : U32)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 32) :
    ∃ out, CrcBody.crc32.init a initial = .ok out ∧
      out.bv = storedEncode 32 a.refin (initial.bv.setWidth a.width.val) := by
  obtain ⟨out,ho,hv⟩ := CrcStage2.init32_spec (algorithmToStage a) initial hw
  refine ⟨out, ho, ?_⟩
  exact hv.trans (rawInit_encoded hw.2 a.refin initial.bv)

theorem finalize32_encoded (a : CrcBody.crc_catalog.Algorithm U32)
    (value : U32) (xorout state : BitVec a.width.val)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 32)
    (hxor : a.xorout.bv = xorout.setWidth 32)
    (hstate : value.bv = storedEncode 32 a.refin state) :
    ∃ out, CrcBody.crc32.finalize a value = .ok out ∧
      out.bv = ((if a.refout then state.reverse else state) ^^^ xorout).setWidth 32 := by
  obtain ⟨out,ho,hv⟩ := CrcStage2.finalize32_spec (algorithmToStage a) value hw
  refine ⟨out,ho,?_⟩
  change out.bv = CrcStage2.rawFinalize a.width.val a.refin a.refout a.xorout.bv value.bv at hv
  rw [hxor,hstate] at hv
  exact hv.trans (rawFinalize_encoded hw.2 a.refin a.refout xorout state)

theorem init64_encoded (a : CrcBody.crc_catalog.Algorithm U64) (initial : U64)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 64) :
    ∃ out, CrcBody.crc64.init a initial = .ok out ∧
      out.bv = storedEncode 64 a.refin (initial.bv.setWidth a.width.val) := by
  obtain ⟨out,ho,hv⟩ := CrcStage2.init64_spec (algorithmToStage a) initial hw
  refine ⟨out, ho, ?_⟩
  exact hv.trans (rawInit_encoded hw.2 a.refin initial.bv)

theorem finalize64_encoded (a : CrcBody.crc_catalog.Algorithm U64)
    (value : U64) (xorout state : BitVec a.width.val)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 64)
    (hxor : a.xorout.bv = xorout.setWidth 64)
    (hstate : value.bv = storedEncode 64 a.refin state) :
    ∃ out, CrcBody.crc64.finalize a value = .ok out ∧
      out.bv = ((if a.refout then state.reverse else state) ^^^ xorout).setWidth 64 := by
  obtain ⟨out,ho,hv⟩ := CrcStage2.finalize64_spec (algorithmToStage a) value hw
  refine ⟨out,ho,?_⟩
  change out.bv = CrcStage2.rawFinalize a.width.val a.refin a.refout a.xorout.bv value.bv at hv
  rw [hxor,hstate] at hv
  exact hv.trans (rawFinalize_encoded hw.2 a.refin a.refout xorout state)

theorem init128_encoded (a : CrcBody.crc_catalog.Algorithm U128) (initial : U128)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 128) :
    ∃ out, CrcBody.crc128.init a initial = .ok out ∧
      out.bv = storedEncode 128 a.refin (initial.bv.setWidth a.width.val) := by
  obtain ⟨out,ho,hv⟩ := CrcStage2.init128_spec (algorithmToStage a) initial hw
  refine ⟨out, ho, ?_⟩
  exact hv.trans (rawInit_encoded hw.2 a.refin initial.bv)

theorem finalize128_encoded (a : CrcBody.crc_catalog.Algorithm U128)
    (value : U128) (xorout state : BitVec a.width.val)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 128)
    (hxor : a.xorout.bv = xorout.setWidth 128)
    (hstate : value.bv = storedEncode 128 a.refin state) :
    ∃ out, CrcBody.crc128.finalize a value = .ok out ∧
      out.bv = ((if a.refout then state.reverse else state) ^^^ xorout).setWidth 128 := by
  obtain ⟨out,ho,hv⟩ := CrcStage2.finalize128_spec (algorithmToStage a) value hw
  refine ⟨out,ho,?_⟩
  change out.bv = CrcStage2.rawFinalize a.width.val a.refin a.refout a.xorout.bv value.bv at hv
  rw [hxor,hstate] at hv
  exact hv.trans (rawFinalize_encoded hw.2 a.refin a.refout xorout state)

theorem init8_eq_encoded (a : CrcBody.crc_catalog.Algorithm U8) (initial : U8)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 8) :
    CrcBody.crc8.init a initial = .ok (UScalar.mk
      (storedEncode 8 a.refin (initial.bv.setWidth a.width.val))) := by
  obtain ⟨out,ho,hv⟩ := init8_encoded a initial hw
  have heq : out = UScalar.mk (ty := .U8)
      (storedEncode 8 a.refin (initial.bv.setWidth a.width.val)) :=
    (UScalar.eq_equiv_bv_eq _ _).mpr hv
  exact ho.trans (congrArg Result.ok heq)

theorem init16_eq_encoded (a : CrcBody.crc_catalog.Algorithm U16) (initial : U16)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 16) :
    CrcBody.crc16.init a initial = .ok (UScalar.mk
      (storedEncode 16 a.refin (initial.bv.setWidth a.width.val))) := by
  obtain ⟨out,ho,hv⟩ := init16_encoded a initial hw
  have heq : out = UScalar.mk (ty := .U16)
      (storedEncode 16 a.refin (initial.bv.setWidth a.width.val)) :=
    (UScalar.eq_equiv_bv_eq _ _).mpr hv
  exact ho.trans (congrArg Result.ok heq)

theorem init32_eq_encoded (a : CrcBody.crc_catalog.Algorithm U32) (initial : U32)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 32) :
    CrcBody.crc32.init a initial = .ok (UScalar.mk
      (storedEncode 32 a.refin (initial.bv.setWidth a.width.val))) := by
  obtain ⟨out,ho,hv⟩ := init32_encoded a initial hw
  have heq : out = UScalar.mk (ty := .U32)
      (storedEncode 32 a.refin (initial.bv.setWidth a.width.val)) :=
    (UScalar.eq_equiv_bv_eq _ _).mpr hv
  exact ho.trans (congrArg Result.ok heq)

theorem init64_eq_encoded (a : CrcBody.crc_catalog.Algorithm U64) (initial : U64)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 64) :
    CrcBody.crc64.init a initial = .ok (UScalar.mk
      (storedEncode 64 a.refin (initial.bv.setWidth a.width.val))) := by
  obtain ⟨out,ho,hv⟩ := init64_encoded a initial hw
  have heq : out = UScalar.mk (ty := .U64)
      (storedEncode 64 a.refin (initial.bv.setWidth a.width.val)) :=
    (UScalar.eq_equiv_bv_eq _ _).mpr hv
  exact ho.trans (congrArg Result.ok heq)

theorem init128_eq_encoded (a : CrcBody.crc_catalog.Algorithm U128) (initial : U128)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 128) :
    CrcBody.crc128.init a initial = .ok (UScalar.mk
      (storedEncode 128 a.refin (initial.bv.setWidth a.width.val))) := by
  obtain ⟨out,ho,hv⟩ := init128_encoded a initial hw
  have heq : out = UScalar.mk (ty := .U128)
      (storedEncode 128 a.refin (initial.bv.setWidth a.width.val)) :=
    (UScalar.eq_equiv_bv_eq _ _).mpr hv
  exact ho.trans (congrArg Result.ok heq)

end CrcWidthEndpoints
