import Anchors

open Aeneas Aeneas.Std
namespace CrcProofs

/-- Actual upstream accessor, valid for every representable stored table. -/
theorem table_u8_l0_spec (c : crc_mono_anchors.crc.CrcU8Table0) :
    ∃ out, crc_mono_anchors.crc.crc8.CrcU8Table0.table0 c = .ok out ∧ out = c.data := by
  exact ⟨c.data, rfl, rfl⟩

/-- Actual upstream accessor, valid for every representable stored table. -/
theorem table_u8_l1_spec (c : crc_mono_anchors.crc.CrcU8Table1) :
    ∃ out, crc_mono_anchors.crc.crc8.CrcU8Table1.table1 c = .ok out ∧ out = c.data := by
  exact ⟨c.data, rfl, rfl⟩

/-- Actual upstream accessor, valid for every representable stored table. -/
theorem table_u8_l16_spec (c : crc_mono_anchors.crc.CrcU8Table16) :
    ∃ out, crc_mono_anchors.crc.crc8.CrcU8Table16.table16 c = .ok out ∧ out = c.data := by
  exact ⟨c.data, rfl, rfl⟩

/-- Actual upstream accessor, valid for every representable stored table. -/
theorem table_u16_l0_spec (c : crc_mono_anchors.crc.CrcU16Table0) :
    ∃ out, crc_mono_anchors.crc.crc16.CrcU16Table0.table0 c = .ok out ∧ out = c.data := by
  exact ⟨c.data, rfl, rfl⟩

/-- Actual upstream accessor, valid for every representable stored table. -/
theorem table_u16_l1_spec (c : crc_mono_anchors.crc.CrcU16Table1) :
    ∃ out, crc_mono_anchors.crc.crc16.CrcU16Table1.table1 c = .ok out ∧ out = c.data := by
  exact ⟨c.data, rfl, rfl⟩

/-- Actual upstream accessor, valid for every representable stored table. -/
theorem table_u16_l16_spec (c : crc_mono_anchors.crc.CrcU16Table16) :
    ∃ out, crc_mono_anchors.crc.crc16.CrcU16Table16.table16 c = .ok out ∧ out = c.data := by
  exact ⟨c.data, rfl, rfl⟩

/-- Actual upstream accessor, valid for every representable stored table. -/
theorem table_u32_l0_spec (c : crc_mono_anchors.crc.CrcU32Table0) :
    ∃ out, crc_mono_anchors.crc.crc32.CrcU32Table0.table0 c = .ok out ∧ out = c.data := by
  exact ⟨c.data, rfl, rfl⟩

/-- Actual upstream accessor, valid for every representable stored table. -/
theorem table_u32_l1_spec (c : crc_mono_anchors.crc.CrcU32Table1) :
    ∃ out, crc_mono_anchors.crc.crc32.CrcU32Table1.table1 c = .ok out ∧ out = c.data := by
  exact ⟨c.data, rfl, rfl⟩

/-- Actual upstream accessor, valid for every representable stored table. -/
theorem table_u32_l16_spec (c : crc_mono_anchors.crc.CrcU32Table16) :
    ∃ out, crc_mono_anchors.crc.crc32.CrcU32Table16.table16 c = .ok out ∧ out = c.data := by
  exact ⟨c.data, rfl, rfl⟩

/-- Actual upstream accessor, valid for every representable stored table. -/
theorem table_u64_l0_spec (c : crc_mono_anchors.crc.CrcU64Table0) :
    ∃ out, crc_mono_anchors.crc.crc64.CrcU64Table0.table0 c = .ok out ∧ out = c.data := by
  exact ⟨c.data, rfl, rfl⟩

/-- Actual upstream accessor, valid for every representable stored table. -/
theorem table_u64_l1_spec (c : crc_mono_anchors.crc.CrcU64Table1) :
    ∃ out, crc_mono_anchors.crc.crc64.CrcU64Table1.table1 c = .ok out ∧ out = c.data := by
  exact ⟨c.data, rfl, rfl⟩

/-- Actual upstream accessor, valid for every representable stored table. -/
theorem table_u64_l16_spec (c : crc_mono_anchors.crc.CrcU64Table16) :
    ∃ out, crc_mono_anchors.crc.crc64.CrcU64Table16.table16 c = .ok out ∧ out = c.data := by
  exact ⟨c.data, rfl, rfl⟩

/-- Actual upstream accessor, valid for every representable stored table. -/
theorem table_u128_l0_spec (c : crc_mono_anchors.crc.CrcU128Table0) :
    ∃ out, crc_mono_anchors.crc.crc128.CrcU128Table0.table0 c = .ok out ∧ out = c.data := by
  exact ⟨c.data, rfl, rfl⟩

/-- Actual upstream accessor, valid for every representable stored table. -/
theorem table_u128_l1_spec (c : crc_mono_anchors.crc.CrcU128Table1) :
    ∃ out, crc_mono_anchors.crc.crc128.CrcU128Table1.table1 c = .ok out ∧ out = c.data := by
  exact ⟨c.data, rfl, rfl⟩

/-- Actual upstream accessor, valid for every representable stored table. -/
theorem table_u128_l16_spec (c : crc_mono_anchors.crc.CrcU128Table16) :
    ∃ out, crc_mono_anchors.crc.crc128.CrcU128Table16.table16 c = .ok out ∧ out = c.data := by
  exact ⟨c.data, rfl, rfl⟩


theorem table_clone_l0_spec (t : crc_mono_anchors.crc.Table0) :
    ∃ out, crc_mono_anchors.crc.Table0.Insts.CoreCloneClone.clone t = .ok out ∧ out = t := by
  exact ⟨t, rfl, rfl⟩

theorem table_clone_l1_spec (t : crc_mono_anchors.crc.Table1) :
    ∃ out, crc_mono_anchors.crc.Table1.Insts.CoreCloneClone.clone t = .ok out ∧ out = t := by
  exact ⟨t, rfl, rfl⟩

theorem table_clone_l16_spec (t : crc_mono_anchors.crc.Table16) :
    ∃ out, crc_mono_anchors.crc.Table16.Insts.CoreCloneClone.clone t = .ok out ∧ out = t := by
  exact ⟨t, rfl, rfl⟩

end CrcProofs
