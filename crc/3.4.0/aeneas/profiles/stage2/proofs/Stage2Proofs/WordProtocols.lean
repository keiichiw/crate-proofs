import CrcBody.Funs
import Stage2Proofs.InitFinalize
open Aeneas Aeneas.Std Result
namespace CrcPublicWords

/-- The three sealed implementation lanes supported by the actual Rust API. -/
def SupportedL (L : Usize) : Prop := L = 0#usize ∨ L = 1#usize ∨ L = 16#usize

def convertAlgorithm {W : Type _} (a : CrcBody.crc_catalog.Algorithm W) :
    CrcStage2.crc_catalog.Algorithm W :=
  ⟨a.width, a.poly, a.init, a.refin, a.refout, a.xorout, a.check, a.residue⟩

theorem init8_eq (a : CrcBody.crc_catalog.Algorithm U8) (v : U8) :
    CrcBody.crc8.init a v = CrcStage2.crc8.init (convertAlgorithm a) v := by rfl

theorem finalize8_eq (a : CrcBody.crc_catalog.Algorithm U8) (v : U8) :
    CrcBody.crc8.finalize a v = CrcStage2.crc8.finalize (convertAlgorithm a) v := by rfl

/-- Actual custom digest initialization preserves the complete current Crc and encodes its word state. -/
theorem digest_with_initial8_spec {L : Usize}
    (self : CrcBody.Crc U8 (CrcBody.Table L) (Array (Array U8 256#usize) L))
    (initial : U8) (_hL : SupportedL L)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 8) :
    ∃ out, CrcBody.crc8.CrcU8Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin initial.bv := by
  obtain ⟨value, hv, hbits⟩ := CrcStage2.init8_spec (convertAlgorithm self.algorithm) initial hw
  refine ⟨⟨self, value⟩, ?_, rfl, hbits⟩
  simp only [CrcBody.crc8.CrcU8Table.digest_with_initial, init8_eq, hv, bind_ok,
    CrcBody.crc8.DigestAU8Table.new]

/-- Actual default digest initialization uses the current algorithm's initial value. -/
theorem digest8_spec {L : Usize}
    (self : CrcBody.Crc U8 (CrcBody.Table L) (Array (Array U8 256#usize) L))
    (hL : SupportedL L)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 8) :
    ∃ out, CrcBody.crc8.CrcU8Table.digest self = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin self.algorithm.init.bv := by
  simpa only [CrcBody.crc8.CrcU8Table.digest] using
    digest_with_initial8_spec self self.algorithm.init hL hw

/-- Actual finalization succeeds on every raw digest word under the public width bound. -/
theorem digest_finalize8_spec {L : Usize}
    (self : CrcBody.Digest U8 (CrcBody.Table L) (Array (Array U8 256#usize) L))
    (_hL : SupportedL L)
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 8) :
    ∃ out, CrcBody.crc8.DigestAU8Table.finalize self = .ok out ∧
      out.bv = CrcStage2.rawFinalize self.crc.algorithm.width.val
        self.crc.algorithm.refin self.crc.algorithm.refout self.crc.algorithm.xorout.bv self.value.bv := by
  simpa only [CrcBody.crc8.DigestAU8Table.finalize, finalize8_eq, convertAlgorithm] using
    CrcStage2.finalize8_spec (convertAlgorithm self.crc.algorithm) self.value hw

theorem init16_eq (a : CrcBody.crc_catalog.Algorithm U16) (v : U16) :
    CrcBody.crc16.init a v = CrcStage2.crc16.init (convertAlgorithm a) v := by rfl

theorem finalize16_eq (a : CrcBody.crc_catalog.Algorithm U16) (v : U16) :
    CrcBody.crc16.finalize a v = CrcStage2.crc16.finalize (convertAlgorithm a) v := by rfl

/-- Actual custom digest initialization preserves the complete current Crc and encodes its word state. -/
theorem digest_with_initial16_spec {L : Usize}
    (self : CrcBody.Crc U16 (CrcBody.Table L) (Array (Array U16 256#usize) L))
    (initial : U16) (_hL : SupportedL L)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 16) :
    ∃ out, CrcBody.crc16.CrcU16Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin initial.bv := by
  obtain ⟨value, hv, hbits⟩ := CrcStage2.init16_spec (convertAlgorithm self.algorithm) initial hw
  refine ⟨⟨self, value⟩, ?_, rfl, hbits⟩
  simp only [CrcBody.crc16.CrcU16Table.digest_with_initial, init16_eq, hv, bind_ok,
    CrcBody.crc16.DigestAU16Table.new]

/-- Actual default digest initialization uses the current algorithm's initial value. -/
theorem digest16_spec {L : Usize}
    (self : CrcBody.Crc U16 (CrcBody.Table L) (Array (Array U16 256#usize) L))
    (hL : SupportedL L)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 16) :
    ∃ out, CrcBody.crc16.CrcU16Table.digest self = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin self.algorithm.init.bv := by
  simpa only [CrcBody.crc16.CrcU16Table.digest] using
    digest_with_initial16_spec self self.algorithm.init hL hw

/-- Actual finalization succeeds on every raw digest word under the public width bound. -/
theorem digest_finalize16_spec {L : Usize}
    (self : CrcBody.Digest U16 (CrcBody.Table L) (Array (Array U16 256#usize) L))
    (_hL : SupportedL L)
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 16) :
    ∃ out, CrcBody.crc16.DigestAU16Table.finalize self = .ok out ∧
      out.bv = CrcStage2.rawFinalize self.crc.algorithm.width.val
        self.crc.algorithm.refin self.crc.algorithm.refout self.crc.algorithm.xorout.bv self.value.bv := by
  simpa only [CrcBody.crc16.DigestAU16Table.finalize, finalize16_eq, convertAlgorithm] using
    CrcStage2.finalize16_spec (convertAlgorithm self.crc.algorithm) self.value hw

theorem init32_eq (a : CrcBody.crc_catalog.Algorithm U32) (v : U32) :
    CrcBody.crc32.init a v = CrcStage2.crc32.init (convertAlgorithm a) v := by rfl

theorem finalize32_eq (a : CrcBody.crc_catalog.Algorithm U32) (v : U32) :
    CrcBody.crc32.finalize a v = CrcStage2.crc32.finalize (convertAlgorithm a) v := by rfl

/-- Actual custom digest initialization preserves the complete current Crc and encodes its word state. -/
theorem digest_with_initial32_spec {L : Usize}
    (self : CrcBody.Crc U32 (CrcBody.Table L) (Array (Array U32 256#usize) L))
    (initial : U32) (_hL : SupportedL L)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 32) :
    ∃ out, CrcBody.crc32.CrcU32Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin initial.bv := by
  obtain ⟨value, hv, hbits⟩ := CrcStage2.init32_spec (convertAlgorithm self.algorithm) initial hw
  refine ⟨⟨self, value⟩, ?_, rfl, hbits⟩
  simp only [CrcBody.crc32.CrcU32Table.digest_with_initial, init32_eq, hv, bind_ok,
    CrcBody.crc32.DigestAU32Table.new]

/-- Actual default digest initialization uses the current algorithm's initial value. -/
theorem digest32_spec {L : Usize}
    (self : CrcBody.Crc U32 (CrcBody.Table L) (Array (Array U32 256#usize) L))
    (hL : SupportedL L)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 32) :
    ∃ out, CrcBody.crc32.CrcU32Table.digest self = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin self.algorithm.init.bv := by
  simpa only [CrcBody.crc32.CrcU32Table.digest] using
    digest_with_initial32_spec self self.algorithm.init hL hw

/-- Actual finalization succeeds on every raw digest word under the public width bound. -/
theorem digest_finalize32_spec {L : Usize}
    (self : CrcBody.Digest U32 (CrcBody.Table L) (Array (Array U32 256#usize) L))
    (_hL : SupportedL L)
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 32) :
    ∃ out, CrcBody.crc32.DigestAU32Table.finalize self = .ok out ∧
      out.bv = CrcStage2.rawFinalize self.crc.algorithm.width.val
        self.crc.algorithm.refin self.crc.algorithm.refout self.crc.algorithm.xorout.bv self.value.bv := by
  simpa only [CrcBody.crc32.DigestAU32Table.finalize, finalize32_eq, convertAlgorithm] using
    CrcStage2.finalize32_spec (convertAlgorithm self.crc.algorithm) self.value hw

theorem init64_eq (a : CrcBody.crc_catalog.Algorithm U64) (v : U64) :
    CrcBody.crc64.init a v = CrcStage2.crc64.init (convertAlgorithm a) v := by rfl

theorem finalize64_eq (a : CrcBody.crc_catalog.Algorithm U64) (v : U64) :
    CrcBody.crc64.finalize a v = CrcStage2.crc64.finalize (convertAlgorithm a) v := by rfl

/-- Actual custom digest initialization preserves the complete current Crc and encodes its word state. -/
theorem digest_with_initial64_spec {L : Usize}
    (self : CrcBody.Crc U64 (CrcBody.Table L) (Array (Array U64 256#usize) L))
    (initial : U64) (_hL : SupportedL L)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 64) :
    ∃ out, CrcBody.crc64.CrcU64Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin initial.bv := by
  obtain ⟨value, hv, hbits⟩ := CrcStage2.init64_spec (convertAlgorithm self.algorithm) initial hw
  refine ⟨⟨self, value⟩, ?_, rfl, hbits⟩
  simp only [CrcBody.crc64.CrcU64Table.digest_with_initial, init64_eq, hv, bind_ok,
    CrcBody.crc64.DigestAU64Table.new]

/-- Actual default digest initialization uses the current algorithm's initial value. -/
theorem digest64_spec {L : Usize}
    (self : CrcBody.Crc U64 (CrcBody.Table L) (Array (Array U64 256#usize) L))
    (hL : SupportedL L)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 64) :
    ∃ out, CrcBody.crc64.CrcU64Table.digest self = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin self.algorithm.init.bv := by
  simpa only [CrcBody.crc64.CrcU64Table.digest] using
    digest_with_initial64_spec self self.algorithm.init hL hw

/-- Actual finalization succeeds on every raw digest word under the public width bound. -/
theorem digest_finalize64_spec {L : Usize}
    (self : CrcBody.Digest U64 (CrcBody.Table L) (Array (Array U64 256#usize) L))
    (_hL : SupportedL L)
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 64) :
    ∃ out, CrcBody.crc64.DigestAU64Table.finalize self = .ok out ∧
      out.bv = CrcStage2.rawFinalize self.crc.algorithm.width.val
        self.crc.algorithm.refin self.crc.algorithm.refout self.crc.algorithm.xorout.bv self.value.bv := by
  simpa only [CrcBody.crc64.DigestAU64Table.finalize, finalize64_eq, convertAlgorithm] using
    CrcStage2.finalize64_spec (convertAlgorithm self.crc.algorithm) self.value hw

theorem init128_eq (a : CrcBody.crc_catalog.Algorithm U128) (v : U128) :
    CrcBody.crc128.init a v = CrcStage2.crc128.init (convertAlgorithm a) v := by rfl

theorem finalize128_eq (a : CrcBody.crc_catalog.Algorithm U128) (v : U128) :
    CrcBody.crc128.finalize a v = CrcStage2.crc128.finalize (convertAlgorithm a) v := by rfl

/-- Actual custom digest initialization preserves the complete current Crc and encodes its word state. -/
theorem digest_with_initial128_spec {L : Usize}
    (self : CrcBody.Crc U128 (CrcBody.Table L) (Array (Array U128 256#usize) L))
    (initial : U128) (_hL : SupportedL L)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 128) :
    ∃ out, CrcBody.crc128.CrcU128Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin initial.bv := by
  obtain ⟨value, hv, hbits⟩ := CrcStage2.init128_spec (convertAlgorithm self.algorithm) initial hw
  refine ⟨⟨self, value⟩, ?_, rfl, hbits⟩
  simp only [CrcBody.crc128.CrcU128Table.digest_with_initial, init128_eq, hv, bind_ok,
    CrcBody.crc128.DigestAU128Table.new]

/-- Actual default digest initialization uses the current algorithm's initial value. -/
theorem digest128_spec {L : Usize}
    (self : CrcBody.Crc U128 (CrcBody.Table L) (Array (Array U128 256#usize) L))
    (hL : SupportedL L)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 128) :
    ∃ out, CrcBody.crc128.CrcU128Table.digest self = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin self.algorithm.init.bv := by
  simpa only [CrcBody.crc128.CrcU128Table.digest] using
    digest_with_initial128_spec self self.algorithm.init hL hw

/-- Actual finalization succeeds on every raw digest word under the public width bound. -/
theorem digest_finalize128_spec {L : Usize}
    (self : CrcBody.Digest U128 (CrcBody.Table L) (Array (Array U128 256#usize) L))
    (_hL : SupportedL L)
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 128) :
    ∃ out, CrcBody.crc128.DigestAU128Table.finalize self = .ok out ∧
      out.bv = CrcStage2.rawFinalize self.crc.algorithm.width.val
        self.crc.algorithm.refin self.crc.algorithm.refout self.crc.algorithm.xorout.bv self.value.bv := by
  simpa only [CrcBody.crc128.DigestAU128Table.finalize, finalize128_eq, convertAlgorithm] using
    CrcStage2.finalize128_spec (convertAlgorithm self.crc.algorithm) self.value hw

end CrcPublicWords
