import Stage2Proofs.Public8
import Stage2Proofs.ReflectMath8
import Stage2Proofs.InitFinalize
open Aeneas Aeneas.Std Result
namespace CrcReflectedPublic8

def Domain (a : CrcBody.crc_catalog.Algorithm U8) : Prop :=
  a.width = 8#u8 ∧ a.refin = true

def reverseScalar (value : U8) : U8 := UScalar.mk value.bv.reverse

@[simp] theorem reverseScalar_bv (value : U8) : (reverseScalar value).bv = value.bv.reverse := rfl

theorem reverse8 (value : U8) :
    CrcBody.core.num.U8.reverse_bits value = .ok (reverseScalar value) := by
  exact CrcStage2.reverse_bits_u8 value

theorem init_eq (a : CrcBody.crc_catalog.Algorithm U8) (initial : U8)
    (ha : Domain a) : CrcBody.crc8.init a initial = .ok (reverseScalar initial) := by
  obtain ⟨hw, hri⟩ := ha
  unfold CrcBody.crc8.init
  simp only [hw, hri, ↓reduceIte, reverse8, bind_ok]
  have h : WP.spec (do let i ← 8#u8 - 8#u8; reverseScalar initial >>> i)
      (fun out => out = reverseScalar initial) := by
    step
    step
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    have hz : i.val = 0 := by omega
    simpa only [hz, BitVec.ushiftRight_zero] using out_post1
  obtain ⟨out, hout, rfl⟩ := crc.total_result h
  exact hout

def finish (a : CrcBody.crc_catalog.Algorithm U8) (state : BitVec 8) : BitVec 8 :=
  (if a.refout then state.reverse else state) ^^^ a.xorout.bv

theorem finalize_eq (a : CrcBody.crc_catalog.Algorithm U8) (value : U8)
    (ha : Domain a) : CrcBody.crc8.finalize a value =
      .ok ((if a.refout then value else reverseScalar value) ^^^ a.xorout) := by
  obtain ⟨hw, hri⟩ := ha
  unfold CrcBody.crc8.finalize
  cases hro : a.refout
  · simp only [hw, hri, hro, Bool.true_xor, Bool.not_false, ↓reduceIte,
      reverse8, bind_ok, Bool.false_eq_true]
    have h : WP.spec (do
        let i ← 8#u8 - 8#u8
        let v ← reverseScalar value >>> i
        .ok (v ^^^ a.xorout))
        (fun out => out = reverseScalar value ^^^ a.xorout) := by
      step
      step
      have hz : i.val = 0 := by omega
      have heq : v = reverseScalar value := by
        apply (UScalar.eq_equiv_bv_eq _ _).mpr
        simpa only [hz, BitVec.ushiftRight_zero] using v_post1
      exact congrArg (fun x : U8 => x ^^^ a.xorout) heq
    obtain ⟨out, hout, rfl⟩ := crc.total_result h
    simpa only [Aeneas.Std.bind_assoc] using hout
  · simp only [hri, hro, Bool.true_xor, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_ok]

 theorem finalize_canonical (a : CrcBody.crc_catalog.Algorithm U8) (value : U8)
    (ha : Domain a) :
    ∃ out, CrcBody.crc8.finalize a value = .ok out ∧ out.bv = finish a value.bv.reverse := by
  refine ⟨(if a.refout then value else reverseScalar value) ^^^ a.xorout, finalize_eq a value ha, ?_⟩
  cases hro : a.refout <;> simp only [finish, hro, Bool.false_eq_true, ↓reduceIte, UScalar.bv_xor,
    reverseScalar, BitVec.reverse_reverse_eq]

def Coherent (self : CrcBody.Crc8) : Prop :=
  CrcReflected8.TableValid self.algorithm.poly.bv (CrcBody.tableFunction self.data)

theorem update_canonical (self : CrcBody.Crc8) (state : U8) (bytes : Slice U8)
    (ht : Coherent self) :
    ∃ out, CrcBody.crc8.CrcU8Table.update self state bytes = .ok out ∧
      out.bv.reverse = CrcReflected8.run self.algorithm.poly.bv state.bv.reverse
        (bytes.val.map UScalar.bv) := by
  obtain ⟨out, hout, hv⟩ := CrcUpdate8.update_table_total self.algorithm self.data bytes state
  have hf := CrcBody.fold8_bv self.data state bytes.val
  have hc := CrcReflected8.lookupRun_correct self.algorithm.poly.bv
    (CrcBody.tableFunction self.data) ht state.bv.reverse (bytes.val.map UScalar.bv)
  have heq : out.bv =
      (CrcReflected8.run self.algorithm.poly.bv state.bv.reverse (bytes.val.map UScalar.bv)).reverse := by
    exact (congrArg UScalar.bv hv).trans (hf.trans (by simpa only [BitVec.reverse_reverse_eq] using hc))
  refine ⟨out, hout, ?_⟩
  exact (congrArg BitVec.reverse heq).trans BitVec.reverse_reverse_eq
theorem checksum_canonical (self : CrcBody.Crc8) (bytes : Slice U8)
    (ha : Domain self.algorithm) (ht : Coherent self) :
    ∃ out, CrcBody.crc8.CrcU8Table.checksum self bytes = .ok out ∧
      out.bv = finish self.algorithm (CrcReflected8.run self.algorithm.poly.bv
        self.algorithm.init.bv (bytes.val.map UScalar.bv)) := by
  obtain ⟨mid, hm, hv⟩ := update_canonical self (reverseScalar self.algorithm.init) bytes ht
  obtain ⟨out, hf, hout⟩ := finalize_canonical self.algorithm mid ha
  refine ⟨out, ?_, hout.trans ?_⟩
  · simp only [CrcBody.crc8.CrcU8Table.checksum, init_eq _ _ ha, hm, bind_ok, hf]
  · apply congrArg (finish self.algorithm)
    simpa only [reverseScalar_bv, BitVec.reverse_reverse_eq] using hv

theorem digest_initial (self : CrcBody.Crc8) (initial : U8)
    (ha : Domain self.algorithm) :
    CrcBody.crc8.CrcU8Table.digest_with_initial self initial =
      .ok ⟨self, reverseScalar initial⟩ := by
  simp only [CrcBody.crc8.CrcU8Table.digest_with_initial, init_eq _ _ ha, bind_ok,
    CrcBody.crc8.DigestAU8Table.new]

theorem digest_update_canonical (self : CrcBody.Digest8) (bytes : Slice U8)
    (_ha : Domain self.crc.algorithm) (ht : Coherent self.crc) :
    ∃ out, CrcBody.crc8.DigestAU8Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv.reverse =
        CrcReflected8.run self.crc.algorithm.poly.bv self.value.bv.reverse
          (bytes.val.map UScalar.bv) := by
  obtain ⟨mid, hm, hv⟩ := update_canonical self.crc self.value bytes ht
  exact ⟨{self with value := mid}, by simp [CrcBody.crc8.DigestAU8Table.update, hm], rfl, hv⟩

theorem digest_protocol_canonical (self : CrcBody.Crc8) (initial : U8) (bytes : Slice U8)
    (ha : Domain self.algorithm) (ht : Coherent self) :
    ∃ start stop out,
      CrcBody.crc8.CrcU8Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc8.DigestAU8Table.update start bytes = .ok stop ∧
      CrcBody.crc8.DigestAU8Table.finalize stop = .ok out ∧
      out.bv = finish self.algorithm
        (CrcReflected8.run self.algorithm.poly.bv initial.bv (bytes.val.map UScalar.bv)) := by
  obtain ⟨stop, hu, hc, hv⟩ := digest_update_canonical
    (⟨self, reverseScalar initial⟩ : CrcBody.Digest8) bytes ha ht
  have hsa : Domain stop.crc.algorithm := by simpa only [hc] using ha
  obtain ⟨out, hf, hout⟩ := finalize_canonical stop.crc.algorithm stop.value hsa
  refine ⟨⟨self, reverseScalar initial⟩, stop, out, digest_initial self initial ha, hu, hf, ?_⟩
  have hvc : stop.value.bv.reverse =
      CrcReflected8.run self.algorithm.poly.bv initial.bv (bytes.val.map UScalar.bv) := by
    simpa only [reverseScalar_bv, BitVec.reverse_reverse_eq] using hv
  simpa only [hc] using hout.trans (congrArg (finish stop.crc.algorithm) hvc)
end CrcReflectedPublic8
