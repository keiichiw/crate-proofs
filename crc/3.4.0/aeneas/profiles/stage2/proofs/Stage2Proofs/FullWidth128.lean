import Stage2Proofs.FullWidthSpec
import Stage2Proofs.Constructor128
import Stage2Proofs.ReflectedConstructor128
import Stage2Proofs.NoTable128
import Stage2Proofs.NoTable128Reflected
open Aeneas Aeneas.Std Result
namespace CrcFullWidth128

def Coherent1 (self : CrcPublic128.Crc128) : Prop :=
  if self.algorithm.refin then CrcReflectedTable128.Coherent self else CrcPublic128.Coherent128 self

theorem checksum_table1 (self : CrcPublic128.Crc128) (bytes : Slice U8)
    (hw : self.algorithm.width = 128#u8) (ht : Coherent1 self) :
    ∃ out, CrcBody.crc128.CrcU128Table.checksum self bytes = .ok out ∧
      out.bv = CrcFullWidthSpec.checksum self.algorithm.refin self.algorithm.refout
        self.algorithm.poly.bv self.algorithm.init.bv self.algorithm.xorout.bv
        (bytes.val.map UScalar.bv) := by
  cases hr : self.algorithm.refin
  · have hc : CrcPublic128.Coherent128 self := by simpa only [Coherent1, hr, Bool.false_eq_true, ↓reduceIte] using ht
    obtain ⟨out, ho, hv⟩ := CrcPublic128.checksum_canonical self bytes ⟨hw,hr⟩ hc
    refine ⟨out, ho, ?_⟩
    exact hv
  · have hc : CrcReflectedTable128.Coherent self := by simpa only [Coherent1, hr, ↓reduceIte] using ht
    obtain ⟨out, ho, hv⟩ := CrcReflectedTable128.checksum_canonical self bytes ⟨hw,hr⟩ hc
    refine ⟨out, ho, ?_⟩
    exact hv
theorem checksum_notable (self : CrcNoTable128.Crc128) (bytes : Slice U8)
    (hw : self.algorithm.width = 128#u8) :
    ∃ out, CrcBody.crc128.CrcU128Table.checksum self bytes = .ok out ∧
      out.bv = CrcFullWidthSpec.checksum self.algorithm.refin self.algorithm.refout
        self.algorithm.poly.bv self.algorithm.init.bv self.algorithm.xorout.bv
        (bytes.val.map UScalar.bv) := by
  cases hr : self.algorithm.refin
  · exact CrcNoTable128.checksum128_canonical self bytes ⟨hw,hr⟩
  · exact CrcReflectedNoTable128.checksum_canonical self bytes ⟨hw,hr⟩

theorem digest_update_table1 (self : CrcPublic128.Digest128) (bytes : Slice U8)
    (hw : self.crc.algorithm.width = 128#u8) (ht : Coherent1 self.crc) :
    ∃ out, CrcBody.crc128.DigestAU128Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧
      CrcFullWidthSpec.decode self.crc.algorithm.refin out.value.bv =
        CrcFullWidthSpec.run self.crc.algorithm.refin self.crc.algorithm.poly.bv
          (CrcFullWidthSpec.decode self.crc.algorithm.refin self.value.bv)
          (bytes.val.map UScalar.bv) := by
  cases hr : self.crc.algorithm.refin
  · have hc : CrcPublic128.Coherent128 self.crc := by simpa only [Coherent1, hr, Bool.false_eq_true, ↓reduceIte] using ht
    exact CrcPublic128.digest_update_canonical self bytes hr hc
  · have hc : CrcReflectedTable128.Coherent self.crc := by simpa only [Coherent1, hr, ↓reduceIte] using ht
    exact CrcReflectedTable128.digest_update_canonical self bytes ⟨hw,hr⟩ hc

theorem digest_update_notable (self : CrcNoTable128.Digest128) (bytes : Slice U8)
    (hw : self.crc.algorithm.width = 128#u8) :
    ∃ out, CrcBody.crc128.DigestAU128Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧
      CrcFullWidthSpec.decode self.crc.algorithm.refin out.value.bv =
        CrcFullWidthSpec.run self.crc.algorithm.refin self.crc.algorithm.poly.bv
          (CrcFullWidthSpec.decode self.crc.algorithm.refin self.value.bv)
          (bytes.val.map UScalar.bv) := by
  cases hr : self.crc.algorithm.refin
  · exact CrcNoTable128.digest128_update_canonical self bytes hw hr
  · exact CrcReflectedNoTable128.digest_update_canonical self bytes ⟨hw,hr⟩

theorem new_table1 (a : CrcBody.crc_catalog.Algorithm U128) (hw : a.width = 128#u8) :
    ∃ out : CrcPublic128.Crc128, CrcBody.crc128.CrcU128Table.new 1#usize a = .ok out ∧
      out.algorithm = a ∧ Coherent1 out := by
  cases hr : a.refin
  · obtain ⟨out,ho,ha,hc⟩ := CrcConstructor128.new128_coherent_nonref a ⟨hw,hr⟩
    exact ⟨out,ho,ha,by simpa only [Coherent1,ha,hr,Bool.false_eq_true,↓reduceIte] using hc⟩
  · obtain ⟨out,ho,ha,hc⟩ := CrcReflectedConstructor128.new_coherent a ⟨hw,hr⟩
    exact ⟨out,ho,ha,by simpa only [Coherent1,ha,hr,↓reduceIte] using hc⟩

theorem new_checksum_table1 (a : CrcBody.crc_catalog.Algorithm U128)
    (hw : a.width = 128#u8) (bytes : Slice U8) :
    ∃ self : CrcPublic128.Crc128, CrcBody.crc128.CrcU128Table.new 1#usize a = .ok self ∧
      ∃ out, CrcBody.crc128.CrcU128Table.checksum self bytes = .ok out ∧
      out.bv = CrcFullWidthSpec.checksum a.refin a.refout a.poly.bv a.init.bv a.xorout.bv
        (bytes.val.map UScalar.bv) := by
  obtain ⟨self,hs,ha,hc⟩ := new_table1 a hw
  refine ⟨self,hs,?_⟩
  simpa only [ha] using checksum_table1 self bytes (ha ▸ hw) hc

theorem digest_initial {L : Usize}
    (self : CrcBody.Crc U128 (CrcBody.Table L) (Array (Array U128 256#usize) L))
    (initial : U128) (hw : self.algorithm.width = 128#u8) :
    ∃ out, CrcBody.crc128.CrcU128Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ CrcFullWidthSpec.decode self.algorithm.refin out.value.bv = initial.bv := by
  cases hr : self.algorithm.refin
  · refine ⟨⟨self,initial⟩, ?_, rfl, rfl⟩
    simp only [CrcBody.crc128.CrcU128Table.digest_with_initial,
      CrcPublic128.init_identity _ _ ⟨hw,hr⟩, bind_ok, CrcBody.crc128.DigestAU128Table.new]
  · refine ⟨⟨self,CrcReflectedPublic128.reverseScalar initial⟩, ?_, rfl, ?_⟩
    · simp only [CrcBody.crc128.CrcU128Table.digest_with_initial,
        CrcReflectedPublic128.init_eq _ _ ⟨hw,hr⟩, bind_ok, CrcBody.crc128.DigestAU128Table.new]
    · exact BitVec.reverse_reverse_eq

theorem digest_default {L : Usize}
    (self : CrcBody.Crc U128 (CrcBody.Table L) (Array (Array U128 256#usize) L))
    (hw : self.algorithm.width = 128#u8) :
    ∃ out, CrcBody.crc128.CrcU128Table.digest self = .ok out ∧
      out.crc = self ∧ CrcFullWidthSpec.decode self.algorithm.refin out.value.bv = self.algorithm.init.bv :=
  digest_initial self self.algorithm.init hw

theorem digest_finalize {L : Usize}
    (self : CrcBody.Digest U128 (CrcBody.Table L) (Array (Array U128 256#usize) L))
    (hw : self.crc.algorithm.width = 128#u8) :
    ∃ out, CrcBody.crc128.DigestAU128Table.finalize self = .ok out ∧
      out.bv = CrcFullWidthSpec.finish self.crc.algorithm.refout self.crc.algorithm.xorout.bv
        (CrcFullWidthSpec.decode self.crc.algorithm.refin self.value.bv) := by
  cases hr : self.crc.algorithm.refin
  · exact CrcPublic128.finalize_total self.crc.algorithm self.value ⟨hw,hr⟩
  · exact CrcReflectedPublic128.finalize_canonical self.crc.algorithm self.value ⟨hw,hr⟩
end CrcFullWidth128
