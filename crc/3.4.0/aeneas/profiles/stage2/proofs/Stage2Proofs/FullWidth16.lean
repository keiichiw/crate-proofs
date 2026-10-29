import Stage2Proofs.NoTableConstructor16
import Stage2Proofs.Constructor16
import Stage2Proofs.ReflectedConstructor16
import Stage2Proofs.NoTable16
import Stage2Proofs.NoTable16Reflected
import Stage2Proofs.FullWidthSpec
open Aeneas Aeneas.Std Result
namespace CrcFullWidth16

def Coherent (self : CrcPublic16.Crc16) : Prop :=
  if self.algorithm.refin then CrcReflectedTable16.Coherent self else CrcPublic16.Coherent16 self

theorem table1_checksum (self : CrcPublic16.Crc16) (bytes : Slice U8)
    (hw : self.algorithm.width = 16#u8) (hc : Coherent self) :
    ∃ out, CrcBody.crc16.CrcU16Table.checksum self bytes = .ok out ∧
      out.bv = CrcFullWidthSpec.checksum self.algorithm.refin self.algorithm.refout
        self.algorithm.poly.bv self.algorithm.init.bv self.algorithm.xorout.bv (bytes.val.map UScalar.bv) := by
  cases hr : self.algorithm.refin with
  | false =>
    have hcoh : CrcPublic16.Coherent16 self := by simpa [Coherent, hr] using hc
    simpa [CrcFullWidthSpec.checksum, CrcFullWidthSpec.finish, CrcFullWidthSpec.run, hr] using
      CrcPublic16.checksum_canonical self bytes ⟨hw,hr⟩ hcoh
  | true =>
    have hcoh : CrcReflectedTable16.Coherent self := by simpa [Coherent, hr] using hc
    simpa [CrcFullWidthSpec.checksum, CrcFullWidthSpec.finish, CrcFullWidthSpec.run,
      CrcReflectedPublic16.finish, hr] using CrcReflectedTable16.checksum_canonical self bytes ⟨hw,hr⟩ hcoh

theorem table1_digest_update (self : CrcPublic16.Digest16) (bytes : Slice U8)
    (hw : self.crc.algorithm.width = 16#u8) (hc : Coherent self.crc) :
    ∃ out, CrcBody.crc16.DigestAU16Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ CrcFullWidthSpec.decode self.crc.algorithm.refin out.value.bv =
        CrcFullWidthSpec.run self.crc.algorithm.refin self.crc.algorithm.poly.bv
          (CrcFullWidthSpec.decode self.crc.algorithm.refin self.value.bv) (bytes.val.map UScalar.bv) := by
  cases hr : self.crc.algorithm.refin with
  | false =>
    have hcoh : CrcPublic16.Coherent16 self.crc := by simpa [Coherent, hr] using hc
    simpa [CrcFullWidthSpec.decode, CrcFullWidthSpec.run, hr] using
      CrcPublic16.digest_update_nonref_canonical self bytes ⟨hw,hr⟩ hcoh
  | true =>
    have hcoh : CrcReflectedTable16.Coherent self.crc := by simpa [Coherent, hr] using hc
    simpa [CrcFullWidthSpec.decode, CrcFullWidthSpec.run, hr] using
      CrcReflectedTable16.digest_update_canonical self bytes ⟨hw,hr⟩ hcoh

theorem table1_protocol (self : CrcPublic16.Crc16) (initial : U16) (bytes : Slice U8)
    (hw : self.algorithm.width = 16#u8) (hc : Coherent self) :
    ∃ start final out,
      CrcBody.crc16.CrcU16Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc16.DigestAU16Table.update start bytes = .ok final ∧
      CrcBody.crc16.DigestAU16Table.finalize final = .ok out ∧
      out.bv = CrcFullWidthSpec.checksum self.algorithm.refin self.algorithm.refout
        self.algorithm.poly.bv initial.bv self.algorithm.xorout.bv (bytes.val.map UScalar.bv) := by
  cases hr : self.algorithm.refin with
  | false =>
    have hcoh : CrcPublic16.Coherent16 self := by simpa [Coherent, hr] using hc
    simpa [CrcFullWidthSpec.checksum, CrcFullWidthSpec.finish, CrcFullWidthSpec.run, hr] using
      CrcPublic16.digest_protocol_canonical self initial bytes ⟨hw,hr⟩ hcoh
  | true =>
    have hcoh : CrcReflectedTable16.Coherent self := by simpa [Coherent, hr] using hc
    simpa [CrcFullWidthSpec.checksum, CrcFullWidthSpec.finish, CrcFullWidthSpec.run,
      CrcReflectedPublic16.finish, hr] using CrcReflectedTable16.digest_protocol_canonical self initial bytes ⟨hw,hr⟩ hcoh

theorem notable_checksum (self : CrcNoTable16.Crc16) (bytes : Slice U8)
    (hw : self.algorithm.width = 16#u8) :
    ∃ out, CrcBody.crc16.CrcU16Table.checksum self bytes = .ok out ∧
      out.bv = CrcFullWidthSpec.checksum self.algorithm.refin self.algorithm.refout
        self.algorithm.poly.bv self.algorithm.init.bv self.algorithm.xorout.bv (bytes.val.map UScalar.bv) := by
  cases hr : self.algorithm.refin with
  | false =>
    simpa [CrcFullWidthSpec.checksum, CrcFullWidthSpec.finish, CrcFullWidthSpec.run, hr] using
      CrcNoTable16.checksum16_canonical self bytes ⟨hw,hr⟩
  | true =>
    simpa [CrcFullWidthSpec.checksum, CrcFullWidthSpec.finish, CrcFullWidthSpec.run,
      CrcReflectedPublic16.finish, hr] using CrcReflectedNoTable16.checksum_canonical self bytes ⟨hw,hr⟩

theorem notable_digest_update (self : CrcNoTable16.Digest16) (bytes : Slice U8)
    (hw : self.crc.algorithm.width = 16#u8) :
    ∃ out, CrcBody.crc16.DigestAU16Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ CrcFullWidthSpec.decode self.crc.algorithm.refin out.value.bv =
        CrcFullWidthSpec.run self.crc.algorithm.refin self.crc.algorithm.poly.bv
          (CrcFullWidthSpec.decode self.crc.algorithm.refin self.value.bv) (bytes.val.map UScalar.bv) := by
  cases hr : self.crc.algorithm.refin with
  | false =>
    simpa [CrcFullWidthSpec.decode, CrcFullWidthSpec.run, hr] using
      CrcNoTable16.digest16_update_canonical self bytes hw hr
  | true =>
    simpa [CrcFullWidthSpec.decode, CrcFullWidthSpec.run, hr] using
      CrcReflectedNoTable16.digest_update_canonical self bytes ⟨hw,hr⟩

theorem notable_protocol (self : CrcNoTable16.Crc16) (initial : U16) (bytes : Slice U8)
    (hw : self.algorithm.width = 16#u8) :
    ∃ start final out,
      CrcBody.crc16.CrcU16Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc16.DigestAU16Table.update start bytes = .ok final ∧
      CrcBody.crc16.DigestAU16Table.finalize final = .ok out ∧
      out.bv = CrcFullWidthSpec.checksum self.algorithm.refin self.algorithm.refout
        self.algorithm.poly.bv initial.bv self.algorithm.xorout.bv (bytes.val.map UScalar.bv) := by
  cases hr : self.algorithm.refin with
  | false =>
    simpa [CrcFullWidthSpec.checksum, CrcFullWidthSpec.finish, CrcFullWidthSpec.run, hr] using
      CrcNoTable16.digest_protocol_canonical self initial bytes ⟨hw,hr⟩
  | true =>
    simpa [CrcFullWidthSpec.checksum, CrcFullWidthSpec.finish, CrcFullWidthSpec.run,
      CrcReflectedPublic16.finish, hr] using CrcReflectedNoTable16.digest_protocol_canonical self initial bytes ⟨hw,hr⟩

theorem table1_new (a : CrcBody.crc_catalog.Algorithm U16) (hw : a.width = 16#u8) :
    ∃ self : CrcPublic16.Crc16, CrcBody.crc16.CrcU16Table.new 1#usize a = .ok self ∧
      self.algorithm = a ∧ Coherent self := by
  cases hr : a.refin with
  | false =>
    obtain ⟨self, hs, heq, hc⟩ := CrcConstructor16.new16_coherent_nonref a ⟨hw,hr⟩
    exact ⟨self,hs,heq,by simpa [Coherent, heq, hr] using hc⟩
  | true =>
    obtain ⟨self, hs, heq, hc⟩ := CrcReflectedConstructor16.new16_coherent a ⟨hw,hr⟩
    exact ⟨self,hs,heq,by simpa [Coherent, heq, hr] using hc⟩

theorem notable_new (a : CrcBody.crc_catalog.Algorithm U16) (hw : a.width = 16#u8) :
    ∃ self : CrcNoTable16.Crc16, CrcBody.crc16.CrcU16Table.new 0#usize a = .ok self ∧ self.algorithm = a :=
  CrcNoTableConstructor16.new_total a hw

theorem new_checksum_table1 (a : CrcBody.crc_catalog.Algorithm U16)
    (hw : a.width = 16#u8) (bytes : Slice U8) :
    ∃ self : CrcPublic16.Crc16, CrcBody.crc16.CrcU16Table.new 1#usize a = .ok self ∧
      ∃ out, CrcBody.crc16.CrcU16Table.checksum self bytes = .ok out ∧
      out.bv = CrcFullWidthSpec.checksum a.refin a.refout a.poly.bv a.init.bv a.xorout.bv
        (bytes.val.map UScalar.bv) := by
  obtain ⟨self,hs,ha,hc⟩ := table1_new a hw
  refine ⟨self,hs,?_⟩
  simpa only [ha] using table1_checksum self bytes (ha ▸ hw) hc

theorem digest_initial {L : Usize}
    (self : CrcBody.Crc U16 (CrcBody.Table L) (Array (Array U16 256#usize) L))
    (initial : U16) (hw : self.algorithm.width = 16#u8) :
    ∃ out, CrcBody.crc16.CrcU16Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ CrcFullWidthSpec.decode self.algorithm.refin out.value.bv = initial.bv := by
  cases hr : self.algorithm.refin
  · refine ⟨⟨self,initial⟩, ?_, rfl, rfl⟩
    simp only [CrcBody.crc16.CrcU16Table.digest_with_initial,
      CrcPublic16.init_identity _ _ ⟨hw,hr⟩, bind_ok, CrcBody.crc16.DigestAU16Table.new]
  · refine ⟨⟨self,CrcReflectedPublic16.reverseScalar initial⟩, ?_, rfl, ?_⟩
    · simp only [CrcBody.crc16.CrcU16Table.digest_with_initial,
        CrcReflectedPublic16.init_eq _ _ ⟨hw,hr⟩, bind_ok, CrcBody.crc16.DigestAU16Table.new]
    · exact BitVec.reverse_reverse_eq

theorem digest_default {L : Usize}
    (self : CrcBody.Crc U16 (CrcBody.Table L) (Array (Array U16 256#usize) L))
    (hw : self.algorithm.width = 16#u8) :
    ∃ out, CrcBody.crc16.CrcU16Table.digest self = .ok out ∧
      out.crc = self ∧ CrcFullWidthSpec.decode self.algorithm.refin out.value.bv = self.algorithm.init.bv :=
  digest_initial self self.algorithm.init hw

theorem digest_finalize {L : Usize}
    (self : CrcBody.Digest U16 (CrcBody.Table L) (Array (Array U16 256#usize) L))
    (hw : self.crc.algorithm.width = 16#u8) :
    ∃ out, CrcBody.crc16.DigestAU16Table.finalize self = .ok out ∧
      out.bv = CrcFullWidthSpec.finish self.crc.algorithm.refout self.crc.algorithm.xorout.bv
        (CrcFullWidthSpec.decode self.crc.algorithm.refin self.value.bv) := by
  cases hr : self.crc.algorithm.refin
  · exact CrcPublic16.finalize_total self.crc.algorithm self.value ⟨hw,hr⟩
  · exact CrcReflectedPublic16.finalize_canonical self.crc.algorithm self.value ⟨hw,hr⟩
end CrcFullWidth16
