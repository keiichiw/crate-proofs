import Stage2Proofs.NoTable16
import Stage2Proofs.NoTable16Reflected
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace CrcNoTableConstructor16
abbrev Data := Array (Array U16 256#usize) 0#usize

theorem empty_loop (reflect : Bool) (poly : U16) (table : Data) :
    WP.spec (CrcBody.table.crc16_table_loop0 reflect poly table 0#usize) (fun _ => True) := by
  unfold CrcBody.table.crc16_table_loop0
  apply loop.spec_decr_nat (measure := fun _ => 0) (inv := fun _ => True)
  · intro x _
    rcases x with ⟨t,i⟩
    unfold CrcBody.table.crc16_table_loop0.body
    simp only [show ¬(0#usize : Usize) > 0#usize by decide, ↓reduceIte, ite_self, WP.spec_ok]
  · trivial

theorem table0_total (poly : U16) (reflect : Bool) :
    ∃ out, CrcBody.table.crc16_table 0#usize 16#u8 poly reflect = .ok out := by
  have h : WP.spec (CrcBody.table.crc16_table 0#usize 16#u8 poly reflect) (fun _ => True) := by
    unfold CrcBody.table.crc16_table
    have hzero : ((16#u8 - 16#u8) : Result U8) = .ok 0#u8 := by rfl
    cases reflect with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, hzero, bind_ok]
      step
      apply WP.spec_bind (empty_loop false poly1 (Array.repeat 0#usize (Array.repeat 256#usize 0#u16)))
      intro out _
      simp only [show ¬(0#usize : Usize) > 1#usize by decide, ↓reduceIte, WP.spec_ok]
    | true =>
      simp only [↓reduceIte, CrcReflectedPublic16.reverse16, hzero, bind_ok]
      step
      apply WP.spec_bind (empty_loop true poly1 (Array.repeat 0#usize (Array.repeat 256#usize 0#u16)))
      intro out _
      simp only [show ¬(0#usize : Usize) > 1#usize by decide, ↓reduceIte, WP.spec_ok]
  obtain ⟨out, hout, _⟩ := crc.total_result h
  exact ⟨out,hout⟩

theorem new_total (a : CrcBody.crc_catalog.Algorithm U16) (hw : a.width = 16#u8) :
    ∃ self : CrcNoTable16.Crc16, CrcBody.crc16.CrcU16Table.new 0#usize a = .ok self ∧
      self.algorithm = a := by
  obtain ⟨table,ht⟩ := table0_total a.poly a.refin
  refine ⟨⟨a,table⟩, ?_, rfl⟩
  simp only [CrcBody.crc16.CrcU16Table.new, hw, ht, bind_ok]
end CrcNoTableConstructor16
