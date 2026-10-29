import Stage2Proofs.Public8
open Aeneas Aeneas.Std Result
namespace CrcRefout8

def NonRef8 (a : CrcBody.crc_catalog.Algorithm U8) : Prop :=
  a.width = 8#u8 ∧ a.refin = false

def reverseScalar (value : U8) : U8 := UScalar.mk value.bv.reverse

theorem reverse8 (value : U8) :
    CrcBody.core.num.U8.reverse_bits value = .ok (reverseScalar value) := by
  simp [CrcBody.core.num.U8.reverse_bits, CrcStage2.core.num.U8.reverse_bits,
    CrcStage2.core.intrinsics.bitreverse, reverseScalar]

theorem init_identity (a : CrcBody.crc_catalog.Algorithm U8) (initial : U8)
    (ha : NonRef8 a) : CrcBody.crc8.init a initial = .ok initial := by
  obtain ⟨hw, hri⟩ := ha
  unfold CrcBody.crc8.init
  simp only [hw, hri, Bool.false_eq_true, ↓reduceIte]
  have h : WP.spec (do let i ← 8#u8 - 8#u8; initial <<< i)
      (fun out => out = initial) := by
    step
    step
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    have hz : i.val = 0 := by omega
    simpa only [hz, BitVec.shiftLeft_zero] using out_post1
  obtain ⟨out, hout, rfl⟩ := crc.total_result h
  exact hout

theorem finalize_eq (a : CrcBody.crc_catalog.Algorithm U8) (value : U8)
    (ha : NonRef8 a) :
    CrcBody.crc8.finalize a value =
      .ok ((if a.refout then reverseScalar value else value) ^^^ a.xorout) := by
  obtain ⟨hw, hri⟩ := ha
  cases hro : a.refout with
  | false => exact CrcBody.finalize8_xor a value ⟨hw, hri, hro⟩
  | true =>
    unfold CrcBody.crc8.finalize
    simp only [hri, hro, Bool.false_xor,
      ↓reduceIte, reverse8, bind_ok]

theorem finalize_total (a : CrcBody.crc_catalog.Algorithm U8) (value : U8)
    (ha : NonRef8 a) :
    ∃ out, CrcBody.crc8.finalize a value = .ok out ∧
      out.bv = (if a.refout then value.bv.reverse else value.bv) ^^^ a.xorout.bv := by
  refine ⟨_, finalize_eq a value ha, ?_⟩
  cases a.refout <;> rfl

theorem checksum_canonical (self : CrcBody.Crc8) (bytes : Slice U8)
    (ha : NonRef8 self.algorithm) (ht : CrcBody.Coherent8 self) :
    ∃ out, CrcBody.crc8.CrcU8Table.checksum self bytes = .ok out ∧
      out.bv = (if self.algorithm.refout then
        (CrcCanonical8.run self.algorithm.poly.bv self.algorithm.init.bv
          (bytes.val.map UScalar.bv)).reverse else
        CrcCanonical8.run self.algorithm.poly.bv self.algorithm.init.bv
          (bytes.val.map UScalar.bv)) ^^^ self.algorithm.xorout.bv := by
  obtain ⟨mid, hm, hv⟩ := CrcBody.update8_canonical self self.algorithm.init bytes ht
  obtain ⟨out, hout, hfin⟩ := finalize_total self.algorithm mid ha
  refine ⟨out, ?_, ?_⟩
  · simp only [CrcBody.crc8.CrcU8Table.checksum, init_identity _ _ ha, hm, hout, bind_ok]
  · simpa only [hv] using hfin

theorem digest_update_canonical (self : CrcBody.Digest8) (bytes : Slice U8)
    (ht : CrcBody.Coherent8 self.crc) :
    ∃ out, CrcBody.crc8.DigestAU8Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv =
        CrcCanonical8.run self.crc.algorithm.poly.bv self.value.bv (bytes.val.map UScalar.bv) := by
  obtain ⟨mid, hm, hv⟩ := CrcBody.update8_canonical self.crc self.value bytes ht
  exact ⟨{ self with value := mid }, by simp [CrcBody.crc8.DigestAU8Table.update, hm], rfl, hv⟩

theorem digest_protocol_canonical (self : CrcBody.Crc8) (initial : U8) (bytes : Slice U8)
    (ha : NonRef8 self.algorithm) (ht : CrcBody.Coherent8 self) :
    ∃ start finish out,
      CrcBody.crc8.CrcU8Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc8.DigestAU8Table.update start bytes = .ok finish ∧
      CrcBody.crc8.DigestAU8Table.finalize finish = .ok out ∧
      out.bv = (if self.algorithm.refout then
        (CrcCanonical8.run self.algorithm.poly.bv initial.bv (bytes.val.map UScalar.bv)).reverse
        else CrcCanonical8.run self.algorithm.poly.bv initial.bv (bytes.val.map UScalar.bv))
        ^^^ self.algorithm.xorout.bv := by
  obtain ⟨finish, hu, hc, hv⟩ := digest_update_canonical (⟨self, initial⟩ : CrcBody.Digest8) bytes ht
  have hfa : NonRef8 finish.crc.algorithm := by simpa only [hc] using ha
  obtain ⟨out, hout, hbv⟩ := finalize_total finish.crc.algorithm finish.value hfa
  refine ⟨⟨self, initial⟩, finish, out, ?_, hu, hout, ?_⟩
  · simp only [CrcBody.crc8.CrcU8Table.digest_with_initial, init_identity _ _ ha,
      bind_ok, CrcBody.crc8.DigestAU8Table.new]
  · simpa only [hc, hv] using hbv
/-- Public canonical contract states the algorithm domain explicitly. -/
theorem digest_update_nonref_canonical (self : CrcBody.Digest8) (bytes : Slice U8)
    (_ha : NonRef8 self.crc.algorithm) (ht : CrcBody.Coherent8 self.crc) :
    ∃ out, CrcBody.crc8.DigestAU8Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv =
        CrcCanonical8.run self.crc.algorithm.poly.bv self.value.bv (bytes.val.map UScalar.bv) :=
  digest_update_canonical self bytes ht
end CrcRefout8
