import CloneFrom0.Anchors
import CloneFrom1.Anchors
import CloneFrom16.Anchors

namespace CrcProofs

/-- Inherited standard Clone::clone_from calls the actual upstream Table::clone. -/
theorem table_clone_from_l0_spec (self source : TableCloneFrom0.crc.Table0) :
    ∃ out, TableCloneFrom0.core.clone.Clone.clone_from.default self source = .ok out ∧ out = source := by
  exact ⟨source, rfl, rfl⟩

/-- Inherited standard Clone::clone_from calls the actual upstream Table::clone. -/
theorem table_clone_from_l1_spec (self source : TableCloneFrom1.crc.Table1) :
    ∃ out, TableCloneFrom1.core.clone.Clone.clone_from.default self source = .ok out ∧ out = source := by
  exact ⟨source, rfl, rfl⟩

/-- Inherited standard Clone::clone_from calls the actual upstream Table::clone. -/
theorem table_clone_from_l16_spec (self source : TableCloneFrom16.crc.Table16) :
    ∃ out, TableCloneFrom16.core.clone.Clone.clone_from.default self source = .ok out ∧ out = source := by
  exact ⟨source, rfl, rfl⟩

end CrcProofs
