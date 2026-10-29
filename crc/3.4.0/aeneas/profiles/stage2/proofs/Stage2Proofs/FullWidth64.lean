import Stage2Proofs.FullWidthSpec
import Stage2Proofs.Constructor64
import Stage2Proofs.ReflectedConstructor64
import Stage2Proofs.Public64
import Stage2Proofs.Public64Reflected
import Stage2Proofs.NoTable64
import Stage2Proofs.NoTable64Reflected
namespace CrcFullWidth64
open Aeneas Aeneas.Std
abbrev Crc := CrcPublic64.Crc64
abbrev Digest := CrcPublic64.Digest64

def Coherent (self : Crc) : Prop :=
  if self.algorithm.refin then CrcReflectedTable64.Coherent self
  else CrcPublic64.Coherent64 self

theorem checksum_table1 (self : Crc) (bytes : Slice U8)
    (hw : self.algorithm.width = 64#u8) (ht : Coherent self) :
    ∃ out, CrcBody.crc64.CrcU64Table.checksum self bytes = .ok out ∧
      out.bv = CrcFullWidthSpec.checksum self.algorithm.refin self.algorithm.refout
        self.algorithm.poly.bv self.algorithm.init.bv self.algorithm.xorout.bv
        (bytes.val.map UScalar.bv) := by
  cases hr : self.algorithm.refin
  · have hc : CrcPublic64.Coherent64 self := by simpa only [Coherent,hr, Bool.false_eq_true,↓reduceIte] using ht
    simpa only [CrcFullWidthSpec.checksum,CrcFullWidthSpec.finish,CrcFullWidthSpec.run,hr,
      Bool.false_eq_true,↓reduceIte] using CrcPublic64.checksum_canonical self bytes ⟨hw,hr⟩ hc
  · have hc : CrcReflectedTable64.Coherent self := by simpa only [Coherent,hr,↓reduceIte] using ht
    simpa only [CrcFullWidthSpec.checksum,CrcFullWidthSpec.finish,CrcFullWidthSpec.run,hr,
      ↓reduceIte,CrcReflectedPublic64.finish] using CrcReflectedTable64.checksum_canonical self bytes ⟨hw,hr⟩ hc

theorem digest_update_table1 (self : Digest) (bytes : Slice U8)
    (hw : self.crc.algorithm.width = 64#u8) (ht : Coherent self.crc) :
    ∃ out, CrcBody.crc64.DigestAU64Table.update self bytes = .ok out ∧ out.crc = self.crc ∧
      CrcFullWidthSpec.decode self.crc.algorithm.refin out.value.bv =
        CrcFullWidthSpec.run self.crc.algorithm.refin self.crc.algorithm.poly.bv
          (CrcFullWidthSpec.decode self.crc.algorithm.refin self.value.bv)
          (bytes.val.map UScalar.bv) := by
  cases hr : self.crc.algorithm.refin
  · have hc : CrcPublic64.Coherent64 self.crc := by simpa only [Coherent,hr,Bool.false_eq_true,↓reduceIte] using ht
    simpa only [CrcFullWidthSpec.decode,CrcFullWidthSpec.run,hr,Bool.false_eq_true,↓reduceIte]
      using CrcPublic64.digest_update_canonical self bytes hr hc
  · have hc : CrcReflectedTable64.Coherent self.crc := by simpa only [Coherent,hr,↓reduceIte] using ht
    simpa only [CrcFullWidthSpec.decode,CrcFullWidthSpec.run,hr,↓reduceIte]
      using CrcReflectedTable64.digest_update_canonical self bytes ⟨hw,hr⟩ hc

theorem checksum_notable (self : CrcNoTable64.Crc64) (bytes : Slice U8)
    (hw : self.algorithm.width = 64#u8) :
    ∃ out, CrcBody.crc64.CrcU64Table.checksum self bytes = .ok out ∧
      out.bv = CrcFullWidthSpec.checksum self.algorithm.refin self.algorithm.refout
        self.algorithm.poly.bv self.algorithm.init.bv self.algorithm.xorout.bv
        (bytes.val.map UScalar.bv) := by
  cases hr : self.algorithm.refin
  · simpa only [CrcFullWidthSpec.checksum,CrcFullWidthSpec.finish,CrcFullWidthSpec.run,hr,
      Bool.false_eq_true,↓reduceIte] using CrcNoTable64.checksum64_canonical self bytes ⟨hw,hr⟩
  · simpa only [CrcFullWidthSpec.checksum,CrcFullWidthSpec.finish,CrcFullWidthSpec.run,hr,
      ↓reduceIte,CrcReflectedPublic64.finish] using CrcReflectedNoTable64.checksum_canonical self bytes ⟨hw,hr⟩

theorem digest_update_notable (self : CrcNoTable64.Digest64) (bytes : Slice U8)
    (hw : self.crc.algorithm.width = 64#u8) :
    ∃ out, CrcBody.crc64.DigestAU64Table.update self bytes = .ok out ∧ out.crc = self.crc ∧
      CrcFullWidthSpec.decode self.crc.algorithm.refin out.value.bv =
        CrcFullWidthSpec.run self.crc.algorithm.refin self.crc.algorithm.poly.bv
          (CrcFullWidthSpec.decode self.crc.algorithm.refin self.value.bv)
          (bytes.val.map UScalar.bv) := by
  cases hr : self.crc.algorithm.refin
  · simpa only [CrcFullWidthSpec.decode,CrcFullWidthSpec.run,hr,Bool.false_eq_true,↓reduceIte]
      using CrcNoTable64.digest64_update_canonical self bytes hw hr
  · simpa only [CrcFullWidthSpec.decode,CrcFullWidthSpec.run,hr,↓reduceIte]
      using CrcReflectedNoTable64.digest_update_canonical self bytes ⟨hw,hr⟩
theorem digest_protocol_table1 (self : Crc) (initial : U64) (bytes : Slice U8)
    (hw : self.algorithm.width = 64#u8) (ht : Coherent self) :
    ∃ start stop out,
      CrcBody.crc64.CrcU64Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc64.DigestAU64Table.update start bytes = .ok stop ∧
      CrcBody.crc64.DigestAU64Table.finalize stop = .ok out ∧
      out.bv = CrcFullWidthSpec.checksum self.algorithm.refin self.algorithm.refout
        self.algorithm.poly.bv initial.bv self.algorithm.xorout.bv (bytes.val.map UScalar.bv) := by
  cases hr : self.algorithm.refin
  · have hc : CrcPublic64.Coherent64 self := by simpa only [Coherent,hr,Bool.false_eq_true,↓reduceIte] using ht
    simpa only [CrcFullWidthSpec.checksum,CrcFullWidthSpec.finish,CrcFullWidthSpec.run,hr,
      Bool.false_eq_true,↓reduceIte] using CrcPublic64.digest_protocol_canonical self initial bytes ⟨hw,hr⟩ hc
  · have hc : CrcReflectedTable64.Coherent self := by simpa only [Coherent,hr,↓reduceIte] using ht
    simpa only [CrcFullWidthSpec.checksum,CrcFullWidthSpec.finish,CrcFullWidthSpec.run,hr,
      ↓reduceIte,CrcReflectedPublic64.finish] using CrcReflectedTable64.digest_protocol_canonical self initial bytes ⟨hw,hr⟩ hc

theorem digest_protocol_notable (self : CrcNoTable64.Crc64) (initial : U64) (bytes : Slice U8)
    (hw : self.algorithm.width = 64#u8) :
    ∃ start stop out,
      CrcBody.crc64.CrcU64Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc64.DigestAU64Table.update start bytes = .ok stop ∧
      CrcBody.crc64.DigestAU64Table.finalize stop = .ok out ∧
      out.bv = CrcFullWidthSpec.checksum self.algorithm.refin self.algorithm.refout
        self.algorithm.poly.bv initial.bv self.algorithm.xorout.bv (bytes.val.map UScalar.bv) := by
  cases hr : self.algorithm.refin
  · simpa only [CrcFullWidthSpec.checksum,CrcFullWidthSpec.finish,CrcFullWidthSpec.run,hr,
      Bool.false_eq_true,↓reduceIte] using CrcNoTable64.digest_protocol_canonical self initial bytes ⟨hw,hr⟩
  · simpa only [CrcFullWidthSpec.checksum,CrcFullWidthSpec.finish,CrcFullWidthSpec.run,hr,
      ↓reduceIte,CrcReflectedPublic64.finish] using CrcReflectedNoTable64.digest_protocol_canonical self initial bytes ⟨hw,hr⟩

theorem new_table1 (a : CrcBody.crc_catalog.Algorithm U64) (hw : a.width = 64#u8) :
    ∃ self : Crc, CrcBody.crc64.CrcU64Table.new 1#usize a = .ok self ∧
      self.algorithm = a ∧ Coherent self := by
  cases hr : a.refin
  · obtain ⟨self,hs,ha,hc⟩ := CrcConstructor64.new64_coherent_nonref a ⟨hw,hr⟩
    exact ⟨self,hs,ha,by simpa only [Coherent,ha,hr,Bool.false_eq_true,↓reduceIte] using hc⟩
  · obtain ⟨self,hs,ha,hc⟩ := CrcReflectedConstructor64.new64_coherent_reflected a ⟨hw,hr⟩
    exact ⟨self,hs,ha,by simpa only [Coherent,ha,hr,↓reduceIte] using hc⟩

theorem new_checksum_table1 (a : CrcBody.crc_catalog.Algorithm U64) (hw : a.width = 64#u8)
    (bytes : Slice U8) :
    ∃ self : Crc, CrcBody.crc64.CrcU64Table.new 1#usize a = .ok self ∧
      ∃ out, CrcBody.crc64.CrcU64Table.checksum self bytes = .ok out ∧
        out.bv = CrcFullWidthSpec.checksum a.refin a.refout a.poly.bv a.init.bv
          a.xorout.bv (bytes.val.map UScalar.bv) := by
  obtain ⟨self,hs,ha,hc⟩  := new_table1 a hw
  refine ⟨self,hs,?_⟩
  simpa only [ha] using checksum_table1 self bytes (ha ▸ hw) hc
theorem digest_initial {L : Usize}
    (self : CrcBody.Crc U64 (CrcBody.Table L) (Array (Array U64 256#usize) L))
    (initial : U64) (hw : self.algorithm.width = 64#u8) :
    ∃ out, CrcBody.crc64.CrcU64Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ CrcFullWidthSpec.decode self.algorithm.refin out.value.bv = initial.bv := by
  cases hr : self.algorithm.refin
  · refine ⟨⟨self,initial⟩, ?_, rfl, rfl⟩
    simp only [CrcBody.crc64.CrcU64Table.digest_with_initial,
      CrcPublic64.init_identity _ _ ⟨hw,hr⟩, bind_ok, CrcBody.crc64.DigestAU64Table.new]
  · refine ⟨⟨self,CrcReflectedPublic64.reverseScalar initial⟩, ?_, rfl, ?_⟩
    · simp only [CrcBody.crc64.CrcU64Table.digest_with_initial,
        CrcReflectedPublic64.init_eq _ _ ⟨hw,hr⟩, bind_ok, CrcBody.crc64.DigestAU64Table.new]
    · exact BitVec.reverse_reverse_eq

theorem digest_default {L : Usize}
    (self : CrcBody.Crc U64 (CrcBody.Table L) (Array (Array U64 256#usize) L))
    (hw : self.algorithm.width = 64#u8) :
    ∃ out, CrcBody.crc64.CrcU64Table.digest self = .ok out ∧
      out.crc = self ∧ CrcFullWidthSpec.decode self.algorithm.refin out.value.bv = self.algorithm.init.bv :=
  digest_initial self self.algorithm.init hw

theorem digest_finalize {L : Usize}
    (self : CrcBody.Digest U64 (CrcBody.Table L) (Array (Array U64 256#usize) L))
    (hw : self.crc.algorithm.width = 64#u8) :
    ∃ out, CrcBody.crc64.DigestAU64Table.finalize self = .ok out ∧
      out.bv = CrcFullWidthSpec.finish self.crc.algorithm.refout self.crc.algorithm.xorout.bv
        (CrcFullWidthSpec.decode self.crc.algorithm.refin self.value.bv) := by
  cases hr : self.crc.algorithm.refin
  · exact CrcPublic64.finalize_total self.crc.algorithm self.value ⟨hw,hr⟩
  · exact CrcReflectedPublic64.finalize_canonical self.crc.algorithm self.value ⟨hw,hr⟩
end CrcFullWidth64
