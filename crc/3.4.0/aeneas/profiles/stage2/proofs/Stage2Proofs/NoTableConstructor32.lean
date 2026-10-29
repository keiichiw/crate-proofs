import Stage2Proofs.FullWidth32
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace CrcNoTableConstructor32
abbrev Table0 := Array (Array U32 256#usize) 0#usize

theorem zero_loop (reflect : Bool) (poly : U32) (table : Table0) :
    WP.spec (CrcBody.table.crc32_table_loop0 reflect poly table 0#usize)
      (fun out => out = table) := by
  unfold CrcBody.table.crc32_table_loop0
  apply loop.spec_decr_nat
    (measure := fun _ : Table0 × Usize => 0)
    (inv := fun x : Table0 × Usize => x.1 = table)
  · intro x hx
    rcases x with ⟨t,i⟩
    dsimp only at hx
    unfold CrcBody.table.crc32_table_loop0.body
    simp only [show ¬(0#usize : Usize) > 0#usize by decide, ↓reduceIte]
    split <;> simpa only [WP.spec_ok] using hx
  · rfl

theorem table_total (a : CrcBody.crc_catalog.Algorithm U32) (hw : a.width = 32#u8) :
    ∃ out : Table0, CrcBody.table.crc32_table 0#usize a.width a.poly a.refin = .ok out := by
  have hp : ∃ p, CrcBody.crc32.init a a.poly = .ok p := by
    cases hr : a.refin
    · exact ⟨a.poly, CrcPublic32.init_identity a a.poly ⟨hw,hr⟩⟩
    · exact ⟨CrcReflectedPublic32.reverseScalar a.poly, CrcReflectedPublic32.init_eq a a.poly ⟨hw,hr⟩⟩
  obtain ⟨p,hp⟩ := hp
  have heq : CrcBody.table.crc32_table 0#usize a.width a.poly a.refin = (do
      let poly ← CrcBody.crc32.init a a.poly
      let t ← CrcBody.table.crc32_table_loop0 a.refin poly
        (Array.repeat 0#usize (Array.repeat 256#usize 0#u32)) 0#usize
      .ok t) := by
    unfold CrcBody.table.crc32_table CrcBody.crc32.init
    simp only [show ¬(0#usize : Usize) > 1#usize by decide, ↓reduceIte]
  obtain ⟨out,ho,_⟩ := crc.total_result (zero_loop a.refin p
    (Array.repeat 0#usize (Array.repeat 256#usize 0#u32)))
  exact ⟨out, by simp only [heq,hp,ho,bind_ok]⟩

theorem new_total (a : CrcBody.crc_catalog.Algorithm U32) (hw : a.width = 32#u8) :
    ∃ self : CrcNoTable32.Crc32, CrcBody.crc32.CrcU32Table.new 0#usize a = .ok self ∧
      self.algorithm = a := by
  obtain ⟨t,ht⟩ := table_total a hw
  exact ⟨⟨a,t⟩, by simp only [CrcBody.crc32.CrcU32Table.new,ht,bind_ok], rfl⟩
theorem new_checksum (a : CrcBody.crc_catalog.Algorithm U32) (hw : a.width = 32#u8)
    (bytes : Slice U8) :
    ∃ self : CrcNoTable32.Crc32, CrcBody.crc32.CrcU32Table.new 0#usize a = .ok self ∧
      ∃ out, CrcBody.crc32.CrcU32Table.checksum self bytes = .ok out ∧
      out.bv = CrcFullWidthSpec.checksum a.refin a.refout a.poly.bv a.init.bv a.xorout.bv
        (bytes.val.map UScalar.bv) := by
  obtain ⟨self,hs,ha⟩ := new_total a hw
  refine ⟨self,hs,?_⟩
  simpa only [ha] using CrcFullWidth32.checksum_notable self bytes (ha ▸ hw)
end CrcNoTableConstructor32
