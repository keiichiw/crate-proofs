import Stage2Proofs.Partial32
open Aeneas Aeneas.Std Result
namespace CrcPartialConstructor32
open CrcWidthEncoding CrcWidthEndpoints
abbrev Table32 := CrcUpdate32.Table

def initialTable : Table32 := Array.repeat 1#usize (Array.repeat 256#usize 0#u32)

/-- Exact equality to the generated source fragment: prepare the polynomial using
    the same reverse/shift operations as init, then execute the original table loop. -/
theorem table_prepared (a : CrcBody.crc_catalog.Algorithm U32) :
    CrcBody.table.crc32_table 1#usize a.width a.poly a.refin =
      (do let poly ← CrcBody.crc32.init a a.poly
          CrcBody.table.crc32_table_loop0 a.refin poly initialTable 0#usize) := by
  unfold CrcBody.table.crc32_table CrcBody.crc32.init initialTable
  simp only [show ¬(1#usize : Usize) > 1#usize by decide, ↓reduceIte, Aeneas.Std.bind_pure]

theorem new_table1 (a : CrcBody.crc_catalog.Algorithm U32)
    (poly : BitVec a.width.val) (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 32)
    (hp : a.poly.bv = poly.setWidth 32) :
    ∃ out : CrcPublic32.Crc32, CrcBody.crc32.CrcU32Table.new 1#usize a = .ok out ∧
      out.algorithm = a ∧ CrcPartial32.Coherent out poly := by
  have hpLow : a.poly.bv.setWidth a.width.val = poly := by
    rw [hp]
    simpa using BitVec.setWidth_setWidth_of_le poly hw.2
  have hi := init32_eq_encoded a a.poly hw
  rw [hpLow] at hi
  cases hr : a.refin
  · simp only [storedEncode,hr,Bool.false_eq_true,↓reduceIte] at hi
    obtain ⟨t,ht,hprefix⟩ := crc.total_result (CrcConstructor32.loop_spec
      (UScalar.mk (encode 32 poly)) initialTable)
    refine ⟨⟨a,t⟩,?_,rfl,?_⟩
    · unfold CrcBody.crc32.CrcU32Table.new
      rw [table_prepared,hi]
      simp only [hr,bind_ok,ht]
    · intro byte
      have hbound : byte.val < 256 := by have h := byte.hmax; scalar_tac
      have hb := hprefix byte hbound
      change (CrcPublic32.tableRead t byte).bv = CrcPartialSpec.tableEntry 32 a.refin poly byte.bv
      simp only [CrcPartialSpec.tableEntry,CrcPartialSpec.physical,storedEncode,
        CrcPartialSpec.byteStep,hr,Bool.false_eq_true,↓reduceIte]
      exact hb.trans (by simpa [encode] using encode_byteStep hw.1 hw.2 poly 0 byte.bv |>.symm)
  · simp only [storedEncode,hr,↓reduceIte] at hi
    obtain ⟨t,ht,hprefix⟩ := crc.total_result (CrcReflectedConstructor32.loop_spec
      (UScalar.mk (encode 32 poly).reverse) initialTable)
    refine ⟨⟨a,t⟩,?_,rfl,?_⟩
    · unfold CrcBody.crc32.CrcU32Table.new
      rw [table_prepared,hi]
      simp only [hr,bind_ok,ht]
    · intro byte
      have hbound : byte.val < 256 := by have h := byte.hmax; scalar_tac
      have hb := hprefix byte hbound
      change (CrcPublic32.tableRead t byte).bv = CrcPartialSpec.tableEntry 32 a.refin poly byte.bv
      simp only [CrcPartialSpec.tableEntry,CrcPartialSpec.physical,storedEncode,
        CrcPartialSpec.byteStep,hr,↓reduceIte]
      have he := encode_reflected_byteStep hw.1 hw.2 poly 0 byte.bv
      have hs : (CrcPublic32.tableRead t byte).bv =
          (CrcReflectedWide.byteStep (encode 32 poly) 0 byte.bv).reverse := by
        rw [CrcReflectedWide.byteStep_injection (by decide)]
        have hzInput : (0 : BitVec 32).reverse ^^^ byte.bv.setWidth 32 = byte.bv.setWidth 32 := by
          apply BitVec.eq_of_getLsbD_eq
          intro i hi
          simp [BitVec.getLsbD_reverse]
        rw [hzInput]
        exact hb
      exact hs.trans (congrArg BitVec.reverse (by simpa [encode] using he.symm))


theorem new_checksum_table1 (a : CrcBody.crc_catalog.Algorithm U32)
    (poly xorout : BitVec a.width.val) (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 32)
    (hp : a.poly.bv = poly.setWidth 32) (hx : a.xorout.bv = xorout.setWidth 32)
    (bytes : Slice U8) :
    ∃ self : CrcPublic32.Crc32, CrcBody.crc32.CrcU32Table.new 1#usize a = .ok self ∧
      ∃ out, CrcBody.crc32.CrcU32Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum a.refin a.refout poly
        (a.init.bv.setWidth a.width.val) xorout (bytes.val.map UScalar.bv)).setWidth 32 := by
  obtain ⟨self,hs,ha,hc⟩ := new_table1 a poly hw hp
  refine ⟨self,hs,?_⟩
  subst a
  exact CrcPartial32.checksum_table1 self bytes poly xorout hw hp hx hc

theorem digest_protocol_table1 (self : CrcPublic32.Crc32)
    (poly xorout : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 32)
    (hp : self.algorithm.poly.bv = poly.setWidth 32)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 32)
    (ht : CrcPartial32.Coherent self poly) (initial : U32) (bytes : Slice U8) :
    ∃ start stop out,
      CrcBody.crc32.CrcU32Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc32.DigestAU32Table.update start bytes = .ok stop ∧
      CrcBody.crc32.DigestAU32Table.finalize stop = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout poly
        (initial.bv.setWidth self.algorithm.width.val) xorout (bytes.val.map UScalar.bv)).setWidth 32 := by
  obtain ⟨init,hi,hib⟩ := init32_encoded self.algorithm initial hw
  obtain ⟨mid,hm,hmb⟩ := CrcPartial32.update_table1 hw.1 hw.2 self poly
    (initial.bv.setWidth self.algorithm.width.val) init bytes hib ht
  generalize hstate : CrcPartialSpec.run self.algorithm.refin poly
    (initial.bv.setWidth self.algorithm.width.val) (bytes.val.map UScalar.bv) = finalState at hmb
  obtain ⟨out,ho,hob⟩ := finalize32_encoded self.algorithm mid xorout finalState hw hx hmb
  refine ⟨(⟨self,init⟩ : CrcPublic32.Digest32),(⟨self,mid⟩ : CrcPublic32.Digest32),out,?_,?_,ho,?_⟩
  · simp only [CrcBody.crc32.CrcU32Table.digest_with_initial,hi,bind_ok,CrcBody.crc32.DigestAU32Table.new]
  · simp only [CrcBody.crc32.DigestAU32Table.update,hm,bind_ok]
  · change out.bv = (CrcFullWidthSpec.finish self.algorithm.refout xorout
      (CrcPartialSpec.run self.algorithm.refin poly
        (initial.bv.setWidth self.algorithm.width.val) (bytes.val.map UScalar.bv))).setWidth 32
    rw [hstate]
    exact hob

theorem new_digest_protocol_table1 (a : CrcBody.crc_catalog.Algorithm U32)
    (poly xorout : BitVec a.width.val) (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 32)
    (hp : a.poly.bv = poly.setWidth 32) (hx : a.xorout.bv = xorout.setWidth 32)
    (initial : U32) (bytes : Slice U8) :
    ∃ self : CrcPublic32.Crc32, CrcBody.crc32.CrcU32Table.new 1#usize a = .ok self ∧
      ∃ start stop out,
      CrcBody.crc32.CrcU32Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc32.DigestAU32Table.update start bytes = .ok stop ∧
      CrcBody.crc32.DigestAU32Table.finalize stop = .ok out ∧
      out.bv = (CrcPartialSpec.checksum a.refin a.refout poly
        (initial.bv.setWidth a.width.val) xorout (bytes.val.map UScalar.bv)).setWidth 32 := by
  obtain ⟨self,hs,ha,hc⟩ := new_table1 a poly hw hp
  refine ⟨self,hs,?_⟩
  subst a
  exact digest_protocol_table1 self poly xorout hw hp hx hc initial bytes

end CrcPartialConstructor32
