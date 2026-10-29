import Stage2Proofs.Partial64
open Aeneas Aeneas.Std Result
namespace CrcPartialConstructor64
open CrcWidthEncoding CrcWidthEndpoints
abbrev Table64 := CrcUpdate64.Table

def initialTable : Table64 := Array.repeat 1#usize (Array.repeat 256#usize 0#u64)

/-- Exact equality to the generated source fragment: prepare the polynomial using
    the same reverse/shift operations as init, then execute the original table loop. -/
theorem table_prepared (a : CrcBody.crc_catalog.Algorithm U64) :
    CrcBody.table.crc64_table 1#usize a.width a.poly a.refin =
      (do let poly ← CrcBody.crc64.init a a.poly
          CrcBody.table.crc64_table_loop0 a.refin poly initialTable 0#usize) := by
  unfold CrcBody.table.crc64_table CrcBody.crc64.init initialTable
  simp only [show ¬(1#usize : Usize) > 1#usize by decide, ↓reduceIte, Aeneas.Std.bind_pure]

theorem new_table1 (a : CrcBody.crc_catalog.Algorithm U64)
    (poly : BitVec a.width.val) (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 64)
    (hp : a.poly.bv = poly.setWidth 64) :
    ∃ out : CrcPublic64.Crc64, CrcBody.crc64.CrcU64Table.new 1#usize a = .ok out ∧
      out.algorithm = a ∧ CrcPartial64.Coherent out poly := by
  have hpLow : a.poly.bv.setWidth a.width.val = poly := by
    rw [hp]
    simpa using BitVec.setWidth_setWidth_of_le poly hw.2
  have hi := init64_eq_encoded a a.poly hw
  rw [hpLow] at hi
  cases hr : a.refin
  · simp only [storedEncode,hr,Bool.false_eq_true,↓reduceIte] at hi
    obtain ⟨t,ht,hprefix⟩ := crc.total_result (CrcConstructor64.loop_spec
      (UScalar.mk (encode 64 poly)) initialTable)
    refine ⟨⟨a,t⟩,?_,rfl,?_⟩
    · unfold CrcBody.crc64.CrcU64Table.new
      rw [table_prepared,hi]
      simp only [hr,bind_ok,ht]
    · simp only [CrcPartial64.Coherent,CrcPartial64.withPoly,CrcFullWidth64.Coherent,
        CrcPublic64.Coherent64,CrcReflectedTable64.Coherent,hr,Bool.false_eq_true,↓reduceIte]
      intro byte
      have hbound : byte.val < 256 := by have h := byte.hmax; scalar_tac
      exact hprefix byte hbound
  · simp only [storedEncode,hr,↓reduceIte] at hi
    obtain ⟨t,ht,hprefix⟩ := crc.total_result (CrcReflectedConstructor64.loop_spec
      (UScalar.mk (encode 64 poly).reverse) initialTable)
    refine ⟨⟨a,t⟩,?_,rfl,?_⟩
    · unfold CrcBody.crc64.CrcU64Table.new
      rw [table_prepared,hi]
      simp only [hr,bind_ok,ht]
    · simp only [CrcPartial64.Coherent,CrcPartial64.withPoly,CrcFullWidth64.Coherent,
        CrcPublic64.Coherent64,CrcReflectedTable64.Coherent,hr,↓reduceIte]
      intro byte
      have hbound : byte.val < 256 := by have h := byte.hmax; scalar_tac
      have hb := hprefix byte hbound
      rw [CrcReflectedWide.byteStep_injection (by decide)]
      have hzInput : (0 : BitVec 64).reverse ^^^ byte.bv.setWidth 64 = byte.bv.setWidth 64 := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp [BitVec.getLsbD_reverse]
      rw [hzInput]
      exact hb
theorem new_checksum (a : CrcBody.crc_catalog.Algorithm U64)
    (poly xorout : BitVec a.width.val) (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 64)
    (hp : a.poly.bv = poly.setWidth 64) (hx : a.xorout.bv = xorout.setWidth 64)
    (bytes : Slice U8) :
    ∃ self : CrcPublic64.Crc64, CrcBody.crc64.CrcU64Table.new 1#usize a = .ok self ∧
      ∃ out, CrcBody.crc64.CrcU64Table.checksum self bytes = .ok out ∧
        out.bv = (CrcPartialSpec.checksum a.refin a.refout poly
          (a.init.bv.setWidth a.width.val) xorout (bytes.val.map UScalar.bv)).setWidth 64 := by
  obtain ⟨self,hnew,halg,hcoh⟩ := new_table1 a poly hw hp
  subst a
  exact ⟨self,hnew,CrcPartial64.checksum_table1 self hw poly xorout hp hx hcoh bytes⟩
end CrcPartialConstructor64
