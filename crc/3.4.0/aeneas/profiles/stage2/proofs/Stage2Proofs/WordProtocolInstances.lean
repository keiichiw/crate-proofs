import Stage2Proofs.WordProtocols
open Aeneas Aeneas.Std Result
namespace CrcPublicWordInstances

/- Each declaration below is the existing word protocol contract specialized to one
   actual sealed lane count. The SupportedL premise is discharged by the selected
   literal; every width premise and result equality is retained unchanged. These
   wrappers adapt the one-theorem-per-API recorder interface without adding a
   mathematical contract or extending canonical message coverage. -/

theorem digest8_lane0_spec
    (self : CrcBody.Crc U8 (CrcBody.Table 0#usize) (Array (Array U8 256#usize) 0#usize))
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 8) :
    ∃ out, CrcBody.crc8.CrcU8Table.digest self = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin self.algorithm.init.bv := by
  exact CrcPublicWords.digest8_spec self (Or.inl rfl) hw

theorem digest8_lane1_spec
    (self : CrcBody.Crc U8 (CrcBody.Table 1#usize) (Array (Array U8 256#usize) 1#usize))
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 8) :
    ∃ out, CrcBody.crc8.CrcU8Table.digest self = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin self.algorithm.init.bv := by
  exact CrcPublicWords.digest8_spec self (Or.inr (Or.inl rfl)) hw

theorem digest8_lane16_spec
    (self : CrcBody.Crc U8 (CrcBody.Table 16#usize) (Array (Array U8 256#usize) 16#usize))
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 8) :
    ∃ out, CrcBody.crc8.CrcU8Table.digest self = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin self.algorithm.init.bv := by
  exact CrcPublicWords.digest8_spec self (Or.inr (Or.inr rfl)) hw

theorem digest_with_initial8_lane0_spec
    (self : CrcBody.Crc U8 (CrcBody.Table 0#usize) (Array (Array U8 256#usize) 0#usize))
    (initial : U8)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 8) :
    ∃ out, CrcBody.crc8.CrcU8Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin initial.bv := by
  exact CrcPublicWords.digest_with_initial8_spec self initial (Or.inl rfl) hw

theorem digest_with_initial8_lane1_spec
    (self : CrcBody.Crc U8 (CrcBody.Table 1#usize) (Array (Array U8 256#usize) 1#usize))
    (initial : U8)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 8) :
    ∃ out, CrcBody.crc8.CrcU8Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin initial.bv := by
  exact CrcPublicWords.digest_with_initial8_spec self initial (Or.inr (Or.inl rfl)) hw

theorem digest_with_initial8_lane16_spec
    (self : CrcBody.Crc U8 (CrcBody.Table 16#usize) (Array (Array U8 256#usize) 16#usize))
    (initial : U8)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 8) :
    ∃ out, CrcBody.crc8.CrcU8Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin initial.bv := by
  exact CrcPublicWords.digest_with_initial8_spec self initial (Or.inr (Or.inr rfl)) hw

theorem digest_finalize8_lane0_spec
    (self : CrcBody.Digest U8 (CrcBody.Table 0#usize) (Array (Array U8 256#usize) 0#usize))
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 8) :
    ∃ out, CrcBody.crc8.DigestAU8Table.finalize self = .ok out ∧
      out.bv = CrcStage2.rawFinalize self.crc.algorithm.width.val
        self.crc.algorithm.refin self.crc.algorithm.refout self.crc.algorithm.xorout.bv self.value.bv := by
  exact CrcPublicWords.digest_finalize8_spec self (Or.inl rfl) hw

theorem digest_finalize8_lane1_spec
    (self : CrcBody.Digest U8 (CrcBody.Table 1#usize) (Array (Array U8 256#usize) 1#usize))
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 8) :
    ∃ out, CrcBody.crc8.DigestAU8Table.finalize self = .ok out ∧
      out.bv = CrcStage2.rawFinalize self.crc.algorithm.width.val
        self.crc.algorithm.refin self.crc.algorithm.refout self.crc.algorithm.xorout.bv self.value.bv := by
  exact CrcPublicWords.digest_finalize8_spec self (Or.inr (Or.inl rfl)) hw

theorem digest_finalize8_lane16_spec
    (self : CrcBody.Digest U8 (CrcBody.Table 16#usize) (Array (Array U8 256#usize) 16#usize))
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 8) :
    ∃ out, CrcBody.crc8.DigestAU8Table.finalize self = .ok out ∧
      out.bv = CrcStage2.rawFinalize self.crc.algorithm.width.val
        self.crc.algorithm.refin self.crc.algorithm.refout self.crc.algorithm.xorout.bv self.value.bv := by
  exact CrcPublicWords.digest_finalize8_spec self (Or.inr (Or.inr rfl)) hw

theorem digest16_lane0_spec
    (self : CrcBody.Crc U16 (CrcBody.Table 0#usize) (Array (Array U16 256#usize) 0#usize))
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 16) :
    ∃ out, CrcBody.crc16.CrcU16Table.digest self = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin self.algorithm.init.bv := by
  exact CrcPublicWords.digest16_spec self (Or.inl rfl) hw

theorem digest16_lane1_spec
    (self : CrcBody.Crc U16 (CrcBody.Table 1#usize) (Array (Array U16 256#usize) 1#usize))
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 16) :
    ∃ out, CrcBody.crc16.CrcU16Table.digest self = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin self.algorithm.init.bv := by
  exact CrcPublicWords.digest16_spec self (Or.inr (Or.inl rfl)) hw

theorem digest16_lane16_spec
    (self : CrcBody.Crc U16 (CrcBody.Table 16#usize) (Array (Array U16 256#usize) 16#usize))
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 16) :
    ∃ out, CrcBody.crc16.CrcU16Table.digest self = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin self.algorithm.init.bv := by
  exact CrcPublicWords.digest16_spec self (Or.inr (Or.inr rfl)) hw

theorem digest_with_initial16_lane0_spec
    (self : CrcBody.Crc U16 (CrcBody.Table 0#usize) (Array (Array U16 256#usize) 0#usize))
    (initial : U16)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 16) :
    ∃ out, CrcBody.crc16.CrcU16Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin initial.bv := by
  exact CrcPublicWords.digest_with_initial16_spec self initial (Or.inl rfl) hw

theorem digest_with_initial16_lane1_spec
    (self : CrcBody.Crc U16 (CrcBody.Table 1#usize) (Array (Array U16 256#usize) 1#usize))
    (initial : U16)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 16) :
    ∃ out, CrcBody.crc16.CrcU16Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin initial.bv := by
  exact CrcPublicWords.digest_with_initial16_spec self initial (Or.inr (Or.inl rfl)) hw

theorem digest_with_initial16_lane16_spec
    (self : CrcBody.Crc U16 (CrcBody.Table 16#usize) (Array (Array U16 256#usize) 16#usize))
    (initial : U16)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 16) :
    ∃ out, CrcBody.crc16.CrcU16Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin initial.bv := by
  exact CrcPublicWords.digest_with_initial16_spec self initial (Or.inr (Or.inr rfl)) hw

theorem digest_finalize16_lane0_spec
    (self : CrcBody.Digest U16 (CrcBody.Table 0#usize) (Array (Array U16 256#usize) 0#usize))
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 16) :
    ∃ out, CrcBody.crc16.DigestAU16Table.finalize self = .ok out ∧
      out.bv = CrcStage2.rawFinalize self.crc.algorithm.width.val
        self.crc.algorithm.refin self.crc.algorithm.refout self.crc.algorithm.xorout.bv self.value.bv := by
  exact CrcPublicWords.digest_finalize16_spec self (Or.inl rfl) hw

theorem digest_finalize16_lane1_spec
    (self : CrcBody.Digest U16 (CrcBody.Table 1#usize) (Array (Array U16 256#usize) 1#usize))
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 16) :
    ∃ out, CrcBody.crc16.DigestAU16Table.finalize self = .ok out ∧
      out.bv = CrcStage2.rawFinalize self.crc.algorithm.width.val
        self.crc.algorithm.refin self.crc.algorithm.refout self.crc.algorithm.xorout.bv self.value.bv := by
  exact CrcPublicWords.digest_finalize16_spec self (Or.inr (Or.inl rfl)) hw

theorem digest_finalize16_lane16_spec
    (self : CrcBody.Digest U16 (CrcBody.Table 16#usize) (Array (Array U16 256#usize) 16#usize))
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 16) :
    ∃ out, CrcBody.crc16.DigestAU16Table.finalize self = .ok out ∧
      out.bv = CrcStage2.rawFinalize self.crc.algorithm.width.val
        self.crc.algorithm.refin self.crc.algorithm.refout self.crc.algorithm.xorout.bv self.value.bv := by
  exact CrcPublicWords.digest_finalize16_spec self (Or.inr (Or.inr rfl)) hw

theorem digest32_lane0_spec
    (self : CrcBody.Crc U32 (CrcBody.Table 0#usize) (Array (Array U32 256#usize) 0#usize))
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 32) :
    ∃ out, CrcBody.crc32.CrcU32Table.digest self = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin self.algorithm.init.bv := by
  exact CrcPublicWords.digest32_spec self (Or.inl rfl) hw

theorem digest32_lane1_spec
    (self : CrcBody.Crc U32 (CrcBody.Table 1#usize) (Array (Array U32 256#usize) 1#usize))
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 32) :
    ∃ out, CrcBody.crc32.CrcU32Table.digest self = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin self.algorithm.init.bv := by
  exact CrcPublicWords.digest32_spec self (Or.inr (Or.inl rfl)) hw

theorem digest32_lane16_spec
    (self : CrcBody.Crc U32 (CrcBody.Table 16#usize) (Array (Array U32 256#usize) 16#usize))
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 32) :
    ∃ out, CrcBody.crc32.CrcU32Table.digest self = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin self.algorithm.init.bv := by
  exact CrcPublicWords.digest32_spec self (Or.inr (Or.inr rfl)) hw

theorem digest_with_initial32_lane0_spec
    (self : CrcBody.Crc U32 (CrcBody.Table 0#usize) (Array (Array U32 256#usize) 0#usize))
    (initial : U32)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 32) :
    ∃ out, CrcBody.crc32.CrcU32Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin initial.bv := by
  exact CrcPublicWords.digest_with_initial32_spec self initial (Or.inl rfl) hw

theorem digest_with_initial32_lane1_spec
    (self : CrcBody.Crc U32 (CrcBody.Table 1#usize) (Array (Array U32 256#usize) 1#usize))
    (initial : U32)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 32) :
    ∃ out, CrcBody.crc32.CrcU32Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin initial.bv := by
  exact CrcPublicWords.digest_with_initial32_spec self initial (Or.inr (Or.inl rfl)) hw

theorem digest_with_initial32_lane16_spec
    (self : CrcBody.Crc U32 (CrcBody.Table 16#usize) (Array (Array U32 256#usize) 16#usize))
    (initial : U32)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 32) :
    ∃ out, CrcBody.crc32.CrcU32Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin initial.bv := by
  exact CrcPublicWords.digest_with_initial32_spec self initial (Or.inr (Or.inr rfl)) hw

theorem digest_finalize32_lane0_spec
    (self : CrcBody.Digest U32 (CrcBody.Table 0#usize) (Array (Array U32 256#usize) 0#usize))
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 32) :
    ∃ out, CrcBody.crc32.DigestAU32Table.finalize self = .ok out ∧
      out.bv = CrcStage2.rawFinalize self.crc.algorithm.width.val
        self.crc.algorithm.refin self.crc.algorithm.refout self.crc.algorithm.xorout.bv self.value.bv := by
  exact CrcPublicWords.digest_finalize32_spec self (Or.inl rfl) hw

theorem digest_finalize32_lane1_spec
    (self : CrcBody.Digest U32 (CrcBody.Table 1#usize) (Array (Array U32 256#usize) 1#usize))
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 32) :
    ∃ out, CrcBody.crc32.DigestAU32Table.finalize self = .ok out ∧
      out.bv = CrcStage2.rawFinalize self.crc.algorithm.width.val
        self.crc.algorithm.refin self.crc.algorithm.refout self.crc.algorithm.xorout.bv self.value.bv := by
  exact CrcPublicWords.digest_finalize32_spec self (Or.inr (Or.inl rfl)) hw

theorem digest_finalize32_lane16_spec
    (self : CrcBody.Digest U32 (CrcBody.Table 16#usize) (Array (Array U32 256#usize) 16#usize))
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 32) :
    ∃ out, CrcBody.crc32.DigestAU32Table.finalize self = .ok out ∧
      out.bv = CrcStage2.rawFinalize self.crc.algorithm.width.val
        self.crc.algorithm.refin self.crc.algorithm.refout self.crc.algorithm.xorout.bv self.value.bv := by
  exact CrcPublicWords.digest_finalize32_spec self (Or.inr (Or.inr rfl)) hw

theorem digest64_lane0_spec
    (self : CrcBody.Crc U64 (CrcBody.Table 0#usize) (Array (Array U64 256#usize) 0#usize))
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 64) :
    ∃ out, CrcBody.crc64.CrcU64Table.digest self = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin self.algorithm.init.bv := by
  exact CrcPublicWords.digest64_spec self (Or.inl rfl) hw

theorem digest64_lane1_spec
    (self : CrcBody.Crc U64 (CrcBody.Table 1#usize) (Array (Array U64 256#usize) 1#usize))
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 64) :
    ∃ out, CrcBody.crc64.CrcU64Table.digest self = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin self.algorithm.init.bv := by
  exact CrcPublicWords.digest64_spec self (Or.inr (Or.inl rfl)) hw

theorem digest64_lane16_spec
    (self : CrcBody.Crc U64 (CrcBody.Table 16#usize) (Array (Array U64 256#usize) 16#usize))
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 64) :
    ∃ out, CrcBody.crc64.CrcU64Table.digest self = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin self.algorithm.init.bv := by
  exact CrcPublicWords.digest64_spec self (Or.inr (Or.inr rfl)) hw

theorem digest_with_initial64_lane0_spec
    (self : CrcBody.Crc U64 (CrcBody.Table 0#usize) (Array (Array U64 256#usize) 0#usize))
    (initial : U64)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 64) :
    ∃ out, CrcBody.crc64.CrcU64Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin initial.bv := by
  exact CrcPublicWords.digest_with_initial64_spec self initial (Or.inl rfl) hw

theorem digest_with_initial64_lane1_spec
    (self : CrcBody.Crc U64 (CrcBody.Table 1#usize) (Array (Array U64 256#usize) 1#usize))
    (initial : U64)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 64) :
    ∃ out, CrcBody.crc64.CrcU64Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin initial.bv := by
  exact CrcPublicWords.digest_with_initial64_spec self initial (Or.inr (Or.inl rfl)) hw

theorem digest_with_initial64_lane16_spec
    (self : CrcBody.Crc U64 (CrcBody.Table 16#usize) (Array (Array U64 256#usize) 16#usize))
    (initial : U64)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 64) :
    ∃ out, CrcBody.crc64.CrcU64Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin initial.bv := by
  exact CrcPublicWords.digest_with_initial64_spec self initial (Or.inr (Or.inr rfl)) hw

theorem digest_finalize64_lane0_spec
    (self : CrcBody.Digest U64 (CrcBody.Table 0#usize) (Array (Array U64 256#usize) 0#usize))
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 64) :
    ∃ out, CrcBody.crc64.DigestAU64Table.finalize self = .ok out ∧
      out.bv = CrcStage2.rawFinalize self.crc.algorithm.width.val
        self.crc.algorithm.refin self.crc.algorithm.refout self.crc.algorithm.xorout.bv self.value.bv := by
  exact CrcPublicWords.digest_finalize64_spec self (Or.inl rfl) hw

theorem digest_finalize64_lane1_spec
    (self : CrcBody.Digest U64 (CrcBody.Table 1#usize) (Array (Array U64 256#usize) 1#usize))
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 64) :
    ∃ out, CrcBody.crc64.DigestAU64Table.finalize self = .ok out ∧
      out.bv = CrcStage2.rawFinalize self.crc.algorithm.width.val
        self.crc.algorithm.refin self.crc.algorithm.refout self.crc.algorithm.xorout.bv self.value.bv := by
  exact CrcPublicWords.digest_finalize64_spec self (Or.inr (Or.inl rfl)) hw

theorem digest_finalize64_lane16_spec
    (self : CrcBody.Digest U64 (CrcBody.Table 16#usize) (Array (Array U64 256#usize) 16#usize))
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 64) :
    ∃ out, CrcBody.crc64.DigestAU64Table.finalize self = .ok out ∧
      out.bv = CrcStage2.rawFinalize self.crc.algorithm.width.val
        self.crc.algorithm.refin self.crc.algorithm.refout self.crc.algorithm.xorout.bv self.value.bv := by
  exact CrcPublicWords.digest_finalize64_spec self (Or.inr (Or.inr rfl)) hw

theorem digest128_lane0_spec
    (self : CrcBody.Crc U128 (CrcBody.Table 0#usize) (Array (Array U128 256#usize) 0#usize))
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 128) :
    ∃ out, CrcBody.crc128.CrcU128Table.digest self = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin self.algorithm.init.bv := by
  exact CrcPublicWords.digest128_spec self (Or.inl rfl) hw

theorem digest128_lane1_spec
    (self : CrcBody.Crc U128 (CrcBody.Table 1#usize) (Array (Array U128 256#usize) 1#usize))
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 128) :
    ∃ out, CrcBody.crc128.CrcU128Table.digest self = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin self.algorithm.init.bv := by
  exact CrcPublicWords.digest128_spec self (Or.inr (Or.inl rfl)) hw

theorem digest128_lane16_spec
    (self : CrcBody.Crc U128 (CrcBody.Table 16#usize) (Array (Array U128 256#usize) 16#usize))
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 128) :
    ∃ out, CrcBody.crc128.CrcU128Table.digest self = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin self.algorithm.init.bv := by
  exact CrcPublicWords.digest128_spec self (Or.inr (Or.inr rfl)) hw

theorem digest_with_initial128_lane0_spec
    (self : CrcBody.Crc U128 (CrcBody.Table 0#usize) (Array (Array U128 256#usize) 0#usize))
    (initial : U128)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 128) :
    ∃ out, CrcBody.crc128.CrcU128Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin initial.bv := by
  exact CrcPublicWords.digest_with_initial128_spec self initial (Or.inl rfl) hw

theorem digest_with_initial128_lane1_spec
    (self : CrcBody.Crc U128 (CrcBody.Table 1#usize) (Array (Array U128 256#usize) 1#usize))
    (initial : U128)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 128) :
    ∃ out, CrcBody.crc128.CrcU128Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin initial.bv := by
  exact CrcPublicWords.digest_with_initial128_spec self initial (Or.inr (Or.inl rfl)) hw

theorem digest_with_initial128_lane16_spec
    (self : CrcBody.Crc U128 (CrcBody.Table 16#usize) (Array (Array U128 256#usize) 16#usize))
    (initial : U128)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 128) :
    ∃ out, CrcBody.crc128.CrcU128Table.digest_with_initial self initial = .ok out ∧
      out.crc = self ∧ out.value.bv =
        CrcStage2.rawInit self.algorithm.width.val self.algorithm.refin initial.bv := by
  exact CrcPublicWords.digest_with_initial128_spec self initial (Or.inr (Or.inr rfl)) hw

theorem digest_finalize128_lane0_spec
    (self : CrcBody.Digest U128 (CrcBody.Table 0#usize) (Array (Array U128 256#usize) 0#usize))
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 128) :
    ∃ out, CrcBody.crc128.DigestAU128Table.finalize self = .ok out ∧
      out.bv = CrcStage2.rawFinalize self.crc.algorithm.width.val
        self.crc.algorithm.refin self.crc.algorithm.refout self.crc.algorithm.xorout.bv self.value.bv := by
  exact CrcPublicWords.digest_finalize128_spec self (Or.inl rfl) hw

theorem digest_finalize128_lane1_spec
    (self : CrcBody.Digest U128 (CrcBody.Table 1#usize) (Array (Array U128 256#usize) 1#usize))
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 128) :
    ∃ out, CrcBody.crc128.DigestAU128Table.finalize self = .ok out ∧
      out.bv = CrcStage2.rawFinalize self.crc.algorithm.width.val
        self.crc.algorithm.refin self.crc.algorithm.refout self.crc.algorithm.xorout.bv self.value.bv := by
  exact CrcPublicWords.digest_finalize128_spec self (Or.inr (Or.inl rfl)) hw

theorem digest_finalize128_lane16_spec
    (self : CrcBody.Digest U128 (CrcBody.Table 16#usize) (Array (Array U128 256#usize) 16#usize))
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 128) :
    ∃ out, CrcBody.crc128.DigestAU128Table.finalize self = .ok out ∧
      out.bv = CrcStage2.rawFinalize self.crc.algorithm.width.val
        self.crc.algorithm.refin self.crc.algorithm.refout self.crc.algorithm.xorout.bv self.value.bv := by
  exact CrcPublicWords.digest_finalize128_spec self (Or.inr (Or.inr rfl)) hw

end CrcPublicWordInstances
