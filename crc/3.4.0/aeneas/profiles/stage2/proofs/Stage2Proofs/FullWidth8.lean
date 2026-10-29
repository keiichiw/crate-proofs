import Stage2Proofs.FullWidthSpec
import Stage2Proofs.Constructor8
import Stage2Proofs.ReflectedConstructor8
import Stage2Proofs.NoTable8Refout
import Stage2Proofs.ReflectedNoTable8
open Aeneas Aeneas.Std Result
namespace CrcFullWidth8

def Coherent1 (self : CrcBody.Crc8) : Prop :=
  if self.algorithm.refin then CrcReflectedPublic8.Coherent self else CrcBody.Coherent8 self

theorem checksum_table1 (self : CrcBody.Crc8) (bytes : Slice U8)
    (hw : self.algorithm.width = 8#u8) (ht : Coherent1 self) :
    ∃ out, CrcBody.crc8.CrcU8Table.checksum self bytes = .ok out ∧
      out.bv = CrcFullWidthSpec.checksum self.algorithm.refin self.algorithm.refout
        self.algorithm.poly.bv self.algorithm.init.bv self.algorithm.xorout.bv
        (bytes.val.map UScalar.bv) := by
  cases hr : self.algorithm.refin
  · have hc : CrcBody.Coherent8 self := by simpa only [Coherent1, hr, Bool.false_eq_true, ↓reduceIte] using ht
    obtain ⟨out, ho, hv⟩ := CrcRefout8.checksum_canonical self bytes ⟨hw,hr⟩ hc
    refine ⟨out, ho, ?_⟩
    exact hv
  · have hc : CrcReflectedPublic8.Coherent self := by simpa only [Coherent1, hr, ↓reduceIte] using ht
    obtain ⟨out, ho, hv⟩ := CrcReflectedPublic8.checksum_canonical self bytes ⟨hw,hr⟩ hc
    refine ⟨out, ho, ?_⟩
    exact hv
theorem checksum_notable (self : CrcNoTable8.Crc8) (bytes : Slice U8)
    (hw : self.algorithm.width = 8#u8) :
    ∃ out, CrcBody.crc8.CrcU8Table.checksum self bytes = .ok out ∧
      out.bv = CrcFullWidthSpec.checksum self.algorithm.refin self.algorithm.refout
        self.algorithm.poly.bv self.algorithm.init.bv self.algorithm.xorout.bv
        (bytes.val.map UScalar.bv) := by
  cases hr : self.algorithm.refin
  · exact CrcNoTable8.checksum_nonref self bytes ⟨hw,hr⟩
  · exact CrcReflectedNoTable8.checksum_canonical self bytes ⟨hw,hr⟩

theorem digest_update_table1 (self : CrcBody.Digest8) (bytes : Slice U8)
    (hw : self.crc.algorithm.width = 8#u8) (ht : Coherent1 self.crc) :
    ∃ out, CrcBody.crc8.DigestAU8Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧
      CrcFullWidthSpec.decode self.crc.algorithm.refin out.value.bv =
        CrcFullWidthSpec.run self.crc.algorithm.refin self.crc.algorithm.poly.bv
          (CrcFullWidthSpec.decode self.crc.algorithm.refin self.value.bv)
          (bytes.val.map UScalar.bv) := by
  cases hr : self.crc.algorithm.refin
  · have hc : CrcBody.Coherent8 self.crc := by simpa only [Coherent1, hr, Bool.false_eq_true, ↓reduceIte] using ht
    exact CrcRefout8.digest_update_nonref_canonical self bytes ⟨hw,hr⟩ hc
  · have hc : CrcReflectedPublic8.Coherent self.crc := by simpa only [Coherent1, hr, ↓reduceIte] using ht
    exact CrcReflectedPublic8.digest_update_canonical self bytes ⟨hw,hr⟩ hc

theorem digest_update_notable (self : CrcNoTable8.Digest8) (bytes : Slice U8)
    (hw : self.crc.algorithm.width = 8#u8) :
    ∃ out, CrcBody.crc8.DigestAU8Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧
      CrcFullWidthSpec.decode self.crc.algorithm.refin out.value.bv =
        CrcFullWidthSpec.run self.crc.algorithm.refin self.crc.algorithm.poly.bv
          (CrcFullWidthSpec.decode self.crc.algorithm.refin self.value.bv)
          (bytes.val.map UScalar.bv) := by
  cases hr : self.crc.algorithm.refin
  · exact CrcNoTable8.digest8_update_canonical self bytes hw hr
  · exact CrcReflectedNoTable8.digest_update_canonical self bytes ⟨hw,hr⟩

theorem new_table1 (a : CrcBody.crc_catalog.Algorithm U8) (hw : a.width = 8#u8) :
    ∃ out : CrcBody.Crc8, CrcBody.crc8.CrcU8Table.new 1#usize a = .ok out ∧
      out.algorithm = a ∧ Coherent1 out := by
  cases hr : a.refin
  · obtain ⟨out,ho,ha,hc⟩ := CrcConstructor8.new8_coherent_nonref a ⟨hw,hr⟩
    exact ⟨out,ho,ha,by simpa only [Coherent1,ha,hr,Bool.false_eq_true,↓reduceIte] using hc⟩
  · obtain ⟨out,ho,ha,hc⟩ := CrcReflectedConstructor8.new_coherent a ⟨hw,hr⟩
    exact ⟨out,ho,ha,by simpa only [Coherent1,ha,hr,↓reduceIte] using hc⟩

theorem new_checksum_table1 (a : CrcBody.crc_catalog.Algorithm U8)
    (hw : a.width = 8#u8) (bytes : Slice U8) :
    ∃ self : CrcBody.Crc8, CrcBody.crc8.CrcU8Table.new 1#usize a = .ok self ∧
      ∃ out, CrcBody.crc8.CrcU8Table.checksum self bytes = .ok out ∧
      out.bv = CrcFullWidthSpec.checksum a.refin a.refout a.poly.bv a.init.bv a.xorout.bv
        (bytes.val.map UScalar.bv) := by
  obtain ⟨self,hs,ha,hc⟩ := new_table1 a hw
  refine ⟨self,hs,?_⟩
  simpa only [ha] using checksum_table1 self bytes (ha ▸ hw) hc

theorem digest_initial {L : Usize}
    (self : CrcBody.Crc U8 (CrcBody.Table L) (Array (Array U8 256#usize) L))
    (initial : U8) (hw : self.algorithm.width = 8#u8) :
    ∃ out, CrcBody.crc8.CrcU8Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ CrcFullWidthSpec.decode self.algorithm.refin out.value.bv = initial.bv := by
  cases hr : self.algorithm.refin
  · refine ⟨⟨self,initial⟩, ?_, rfl, rfl⟩
    simp only [CrcBody.crc8.CrcU8Table.digest_with_initial,
      CrcRefout8.init_identity _ _ ⟨hw,hr⟩, bind_ok, CrcBody.crc8.DigestAU8Table.new]
  · refine ⟨⟨self,CrcReflectedPublic8.reverseScalar initial⟩, ?_, rfl, ?_⟩
    · simp only [CrcBody.crc8.CrcU8Table.digest_with_initial,
        CrcReflectedPublic8.init_eq _ _ ⟨hw,hr⟩, bind_ok, CrcBody.crc8.DigestAU8Table.new]
    · exact BitVec.reverse_reverse_eq

theorem digest_default {L : Usize}
    (self : CrcBody.Crc U8 (CrcBody.Table L) (Array (Array U8 256#usize) L))
    (hw : self.algorithm.width = 8#u8) :
    ∃ out, CrcBody.crc8.CrcU8Table.digest self = .ok out ∧
      out.crc = self ∧ CrcFullWidthSpec.decode self.algorithm.refin out.value.bv = self.algorithm.init.bv :=
  digest_initial self self.algorithm.init hw

theorem digest_finalize {L : Usize}
    (self : CrcBody.Digest U8 (CrcBody.Table L) (Array (Array U8 256#usize) L))
    (hw : self.crc.algorithm.width = 8#u8) :
    ∃ out, CrcBody.crc8.DigestAU8Table.finalize self = .ok out ∧
      out.bv = CrcFullWidthSpec.finish self.crc.algorithm.refout self.crc.algorithm.xorout.bv
        (CrcFullWidthSpec.decode self.crc.algorithm.refin self.value.bv) := by
  cases hr : self.crc.algorithm.refin
  · exact CrcRefout8.finalize_total self.crc.algorithm self.value ⟨hw,hr⟩
  · exact CrcReflectedPublic8.finalize_canonical self.crc.algorithm self.value ⟨hw,hr⟩
end CrcFullWidth8
