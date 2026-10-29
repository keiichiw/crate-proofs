import Stage2Proofs.Partial128
open Aeneas Aeneas.Std Result
namespace CrcPartialConstructor128
open CrcWidthEncoding CrcWidthEndpoints
abbrev Table128 := CrcUpdate128.Table

def initialTable : Table128 := Array.repeat 1#usize (Array.repeat 256#usize 0#u128)

/-- Exact equality to the generated source fragment: prepare the polynomial using
    the same reverse/shift operations as init, then execute the original table loop. -/
theorem table_prepared (a : CrcBody.crc_catalog.Algorithm U128) :
    CrcBody.table.crc128_table 1#usize a.width a.poly a.refin =
      (do let poly ← CrcBody.crc128.init a a.poly
          CrcBody.table.crc128_table_loop0 a.refin poly initialTable 0#usize) := by
  unfold CrcBody.table.crc128_table CrcBody.crc128.init initialTable
  simp only [show ¬(1#usize : Usize) > 1#usize by decide, ↓reduceIte, Aeneas.Std.bind_pure]

theorem new_table1 (a : CrcBody.crc_catalog.Algorithm U128)
    (poly : BitVec a.width.val) (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 128)
    (hp : a.poly.bv = poly.setWidth 128) :
    ∃ out : CrcPublic128.Crc128, CrcBody.crc128.CrcU128Table.new 1#usize a = .ok out ∧
      out.algorithm = a ∧ CrcPartial128.Coherent out poly := by
  have hpLow : a.poly.bv.setWidth a.width.val = poly := by
    rw [hp]
    simpa using BitVec.setWidth_setWidth_of_le poly hw.2
  have hi := init128_eq_encoded a a.poly hw
  rw [hpLow] at hi
  cases hr : a.refin
  · simp only [storedEncode,hr,Bool.false_eq_true,↓reduceIte] at hi
    obtain ⟨t,ht,hprefix⟩ := crc.total_result (CrcConstructor128.loop_spec
      (UScalar.mk (encode 128 poly)) initialTable)
    refine ⟨⟨a,t⟩,?_,rfl,?_⟩
    · unfold CrcBody.crc128.CrcU128Table.new
      rw [table_prepared,hi]
      simp only [hr,bind_ok,ht]
    · intro byte
      have hbound : byte.val < 256 := by have h := byte.hmax; scalar_tac
      have hb := hprefix byte hbound
      change (CrcPublic128.tableRead t byte).bv = CrcPartialSpec.tableEntry 128 a.refin poly byte.bv
      simp only [CrcPartialSpec.tableEntry,CrcPartialSpec.physical,storedEncode,
        CrcPartialSpec.byteStep,hr,Bool.false_eq_true,↓reduceIte]
      exact hb.trans (by simpa [encode] using encode_byteStep hw.1 hw.2 poly 0 byte.bv |>.symm)
  · simp only [storedEncode,hr,↓reduceIte] at hi
    obtain ⟨t,ht,hprefix⟩ := crc.total_result (CrcReflectedConstructor128.loop_spec
      (UScalar.mk (encode 128 poly).reverse) initialTable)
    refine ⟨⟨a,t⟩,?_,rfl,?_⟩
    · unfold CrcBody.crc128.CrcU128Table.new
      rw [table_prepared,hi]
      simp only [hr,bind_ok,ht]
    · intro byte
      have hbound : byte.val < 256 := by have h := byte.hmax; scalar_tac
      have hb := hprefix byte hbound
      change (CrcPublic128.tableRead t byte).bv = CrcPartialSpec.tableEntry 128 a.refin poly byte.bv
      simp only [CrcPartialSpec.tableEntry,CrcPartialSpec.physical,storedEncode,
        CrcPartialSpec.byteStep,hr,↓reduceIte]
      have he := encode_reflected_byteStep hw.1 hw.2 poly 0 byte.bv
      have hs : (CrcPublic128.tableRead t byte).bv =
          (CrcReflectedWide.byteStep (encode 128 poly) 0 byte.bv).reverse := by
        rw [CrcReflectedWide.byteStep_injection (by decide)]
        have hzInput : (0 : BitVec 128).reverse ^^^ byte.bv.setWidth 128 = byte.bv.setWidth 128 := by
          apply BitVec.eq_of_getLsbD_eq
          intro i hi
          simp [BitVec.getLsbD_reverse]
        rw [hzInput]
        exact hb
      exact hs.trans (congrArg BitVec.reverse (by simpa [encode] using he.symm))


theorem new_checksum_table1 (a : CrcBody.crc_catalog.Algorithm U128)
    (poly xorout : BitVec a.width.val) (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 128)
    (hp : a.poly.bv = poly.setWidth 128) (hx : a.xorout.bv = xorout.setWidth 128)
    (bytes : Slice U8) :
    ∃ self : CrcPublic128.Crc128, CrcBody.crc128.CrcU128Table.new 1#usize a = .ok self ∧
      ∃ out, CrcBody.crc128.CrcU128Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum a.refin a.refout poly
        (a.init.bv.setWidth a.width.val) xorout (bytes.val.map UScalar.bv)).setWidth 128 := by
  obtain ⟨self,hs,ha,hc⟩ := new_table1 a poly hw hp
  refine ⟨self,hs,?_⟩
  subst a
  exact CrcPartial128.checksum_table1 self bytes poly xorout hw hp hx hc

theorem digest_protocol_table1 (self : CrcPublic128.Crc128)
    (poly xorout : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 128)
    (_hp : self.algorithm.poly.bv = poly.setWidth 128)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 128)
    (ht : CrcPartial128.Coherent self poly) (initial : U128) (bytes : Slice U8) :
    ∃ start stop out,
      CrcBody.crc128.CrcU128Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc128.DigestAU128Table.update start bytes = .ok stop ∧
      CrcBody.crc128.DigestAU128Table.finalize stop = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout poly
        (initial.bv.setWidth self.algorithm.width.val) xorout (bytes.val.map UScalar.bv)).setWidth 128 := by
  obtain ⟨init,hi,hib⟩ := init128_encoded self.algorithm initial hw
  obtain ⟨mid,hm,hmb⟩ := CrcPartial128.update_table1 hw.1 hw.2 self poly
    (initial.bv.setWidth self.algorithm.width.val) init bytes hib ht
  generalize hstate : CrcPartialSpec.run self.algorithm.refin poly
    (initial.bv.setWidth self.algorithm.width.val) (bytes.val.map UScalar.bv) = finalState at hmb
  obtain ⟨out,ho,hob⟩ := finalize128_encoded self.algorithm mid xorout finalState hw hx hmb
  refine ⟨(⟨self,init⟩ : CrcPublic128.Digest128),(⟨self,mid⟩ : CrcPublic128.Digest128),out,?_,?_,ho,?_⟩
  · simp only [CrcBody.crc128.CrcU128Table.digest_with_initial,hi,bind_ok,CrcBody.crc128.DigestAU128Table.new]
  · simp only [CrcBody.crc128.DigestAU128Table.update,hm,bind_ok]
  · change out.bv = (CrcFullWidthSpec.finish self.algorithm.refout xorout
      (CrcPartialSpec.run self.algorithm.refin poly
        (initial.bv.setWidth self.algorithm.width.val) (bytes.val.map UScalar.bv))).setWidth 128
    rw [hstate]
    exact hob

theorem new_digest_protocol_table1 (a : CrcBody.crc_catalog.Algorithm U128)
    (poly xorout : BitVec a.width.val) (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 128)
    (hp : a.poly.bv = poly.setWidth 128) (hx : a.xorout.bv = xorout.setWidth 128)
    (initial : U128) (bytes : Slice U8) :
    ∃ self : CrcPublic128.Crc128, CrcBody.crc128.CrcU128Table.new 1#usize a = .ok self ∧
      ∃ start stop out,
      CrcBody.crc128.CrcU128Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc128.DigestAU128Table.update start bytes = .ok stop ∧
      CrcBody.crc128.DigestAU128Table.finalize stop = .ok out ∧
      out.bv = (CrcPartialSpec.checksum a.refin a.refout poly
        (initial.bv.setWidth a.width.val) xorout (bytes.val.map UScalar.bv)).setWidth 128 := by
  obtain ⟨self,hs,ha,hc⟩ := new_table1 a poly hw hp
  refine ⟨self,hs,?_⟩
  subst a
  exact digest_protocol_table1 self poly xorout hw hp hx hc initial bytes

end CrcPartialConstructor128
