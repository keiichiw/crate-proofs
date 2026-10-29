import Stage2Proofs.FullWidthSpec
import Stage2Proofs.Constructor32
import Stage2Proofs.ReflectedConstructor32
import Stage2Proofs.NoTable32
import Stage2Proofs.NoTable32Reflected
open Aeneas Aeneas.Std Result
namespace CrcFullWidth32

def Coherent1 (self : CrcPublic32.Crc32) : Prop :=
  if self.algorithm.refin then CrcReflectedTable32.Coherent self else CrcPublic32.Coherent32 self

theorem checksum_table1 (self : CrcPublic32.Crc32) (bytes : Slice U8)
    (hw : self.algorithm.width = 32#u8) (ht : Coherent1 self) :
    ∃ out, CrcBody.crc32.CrcU32Table.checksum self bytes = .ok out ∧
      out.bv = CrcFullWidthSpec.checksum self.algorithm.refin self.algorithm.refout
        self.algorithm.poly.bv self.algorithm.init.bv self.algorithm.xorout.bv
        (bytes.val.map UScalar.bv) := by
  cases hr : self.algorithm.refin
  · have hc : CrcPublic32.Coherent32 self := by simpa only [Coherent1, hr, Bool.false_eq_true, ↓reduceIte] using ht
    obtain ⟨out, ho, hv⟩ := CrcPublic32.checksum_canonical self bytes ⟨hw,hr⟩ hc
    refine ⟨out, ho, ?_⟩
    exact hv
  · have hc : CrcReflectedTable32.Coherent self := by simpa only [Coherent1, hr, ↓reduceIte] using ht
    obtain ⟨out, ho, hv⟩ := CrcReflectedTable32.checksum_canonical self bytes ⟨hw,hr⟩ hc
    refine ⟨out, ho, ?_⟩
    exact hv
theorem checksum_notable (self : CrcNoTable32.Crc32) (bytes : Slice U8)
    (hw : self.algorithm.width = 32#u8) :
    ∃ out, CrcBody.crc32.CrcU32Table.checksum self bytes = .ok out ∧
      out.bv = CrcFullWidthSpec.checksum self.algorithm.refin self.algorithm.refout
        self.algorithm.poly.bv self.algorithm.init.bv self.algorithm.xorout.bv
        (bytes.val.map UScalar.bv) := by
  cases hr : self.algorithm.refin
  · exact CrcNoTable32.checksum32_canonical self bytes ⟨hw,hr⟩
  · exact CrcReflectedNoTable32.checksum_canonical self bytes ⟨hw,hr⟩

theorem digest_update_table1 (self : CrcPublic32.Digest32) (bytes : Slice U8)
    (hw : self.crc.algorithm.width = 32#u8) (ht : Coherent1 self.crc) :
    ∃ out, CrcBody.crc32.DigestAU32Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧
      CrcFullWidthSpec.decode self.crc.algorithm.refin out.value.bv =
        CrcFullWidthSpec.run self.crc.algorithm.refin self.crc.algorithm.poly.bv
          (CrcFullWidthSpec.decode self.crc.algorithm.refin self.value.bv)
          (bytes.val.map UScalar.bv) := by
  cases hr : self.crc.algorithm.refin
  · have hc : CrcPublic32.Coherent32 self.crc := by simpa only [Coherent1, hr, Bool.false_eq_true, ↓reduceIte] using ht
    exact CrcPublic32.digest_update_nonref_canonical self bytes ⟨hw,hr⟩ hc
  · have hc : CrcReflectedTable32.Coherent self.crc := by simpa only [Coherent1, hr, ↓reduceIte] using ht
    exact CrcReflectedTable32.digest_update_canonical self bytes ⟨hw,hr⟩ hc

theorem digest_update_notable (self : CrcNoTable32.Digest32) (bytes : Slice U8)
    (hw : self.crc.algorithm.width = 32#u8) :
    ∃ out, CrcBody.crc32.DigestAU32Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧
      CrcFullWidthSpec.decode self.crc.algorithm.refin out.value.bv =
        CrcFullWidthSpec.run self.crc.algorithm.refin self.crc.algorithm.poly.bv
          (CrcFullWidthSpec.decode self.crc.algorithm.refin self.value.bv)
          (bytes.val.map UScalar.bv) := by
  cases hr : self.crc.algorithm.refin
  · exact CrcNoTable32.digest32_update_canonical self bytes hw hr
  · exact CrcReflectedNoTable32.digest_update_canonical self bytes ⟨hw,hr⟩

theorem new_table1 (a : CrcBody.crc_catalog.Algorithm U32) (hw : a.width = 32#u8) :
    ∃ out : CrcPublic32.Crc32, CrcBody.crc32.CrcU32Table.new 1#usize a = .ok out ∧
      out.algorithm = a ∧ Coherent1 out := by
  cases hr : a.refin
  · obtain ⟨out,ho,ha,hc⟩ := CrcConstructor32.new32_coherent_nonref a ⟨hw,hr⟩
    exact ⟨out,ho,ha,by simpa only [Coherent1,ha,hr,Bool.false_eq_true,↓reduceIte] using hc⟩
  · obtain ⟨out,ho,ha,hc⟩ := CrcReflectedConstructor32.new_coherent a ⟨hw,hr⟩
    exact ⟨out,ho,ha,by simpa only [Coherent1,ha,hr,↓reduceIte] using hc⟩

theorem new_checksum_table1 (a : CrcBody.crc_catalog.Algorithm U32)
    (hw : a.width = 32#u8) (bytes : Slice U8) :
    ∃ self : CrcPublic32.Crc32, CrcBody.crc32.CrcU32Table.new 1#usize a = .ok self ∧
      ∃ out, CrcBody.crc32.CrcU32Table.checksum self bytes = .ok out ∧
      out.bv = CrcFullWidthSpec.checksum a.refin a.refout a.poly.bv a.init.bv a.xorout.bv
        (bytes.val.map UScalar.bv) := by
  obtain ⟨self,hs,ha,hc⟩ := new_table1 a hw
  refine ⟨self,hs,?_⟩
  simpa only [ha] using checksum_table1 self bytes (ha ▸ hw) hc

theorem digest_initial {L : Usize}
    (self : CrcBody.Crc U32 (CrcBody.Table L) (Array (Array U32 256#usize) L))
    (initial : U32) (hw : self.algorithm.width = 32#u8) :
    ∃ out, CrcBody.crc32.CrcU32Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ CrcFullWidthSpec.decode self.algorithm.refin out.value.bv = initial.bv := by
  cases hr : self.algorithm.refin
  · refine ⟨⟨self,initial⟩, ?_, rfl, rfl⟩
    simp only [CrcBody.crc32.CrcU32Table.digest_with_initial,
      CrcPublic32.init_identity _ _ ⟨hw,hr⟩, bind_ok, CrcBody.crc32.DigestAU32Table.new]
  · refine ⟨⟨self,CrcReflectedPublic32.reverseScalar initial⟩, ?_, rfl, ?_⟩
    · simp only [CrcBody.crc32.CrcU32Table.digest_with_initial,
        CrcReflectedPublic32.init_eq _ _ ⟨hw,hr⟩, bind_ok, CrcBody.crc32.DigestAU32Table.new]
    · exact BitVec.reverse_reverse_eq

theorem digest_default {L : Usize}
    (self : CrcBody.Crc U32 (CrcBody.Table L) (Array (Array U32 256#usize) L))
    (hw : self.algorithm.width = 32#u8) :
    ∃ out, CrcBody.crc32.CrcU32Table.digest self = .ok out ∧
      out.crc = self ∧ CrcFullWidthSpec.decode self.algorithm.refin out.value.bv = self.algorithm.init.bv :=
  digest_initial self self.algorithm.init hw

theorem digest_finalize {L : Usize}
    (self : CrcBody.Digest U32 (CrcBody.Table L) (Array (Array U32 256#usize) L))
    (hw : self.crc.algorithm.width = 32#u8) :
    ∃ out, CrcBody.crc32.DigestAU32Table.finalize self = .ok out ∧
      out.bv = CrcFullWidthSpec.finish self.crc.algorithm.refout self.crc.algorithm.xorout.bv
        (CrcFullWidthSpec.decode self.crc.algorithm.refin self.value.bv) := by
  cases hr : self.crc.algorithm.refin
  · exact CrcPublic32.finalize_total self.crc.algorithm self.value ⟨hw,hr⟩
  · exact CrcReflectedPublic32.finalize_canonical self.crc.algorithm self.value ⟨hw,hr⟩
end CrcFullWidth32
