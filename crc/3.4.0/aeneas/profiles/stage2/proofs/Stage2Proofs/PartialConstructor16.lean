import Stage2Proofs.Partial16
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace CrcPartialConstructor16

theorem entry_nonref {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 16) (poly : BitVec w) (byte : BitVec 8) :
    CrcPartialSpec.tableEntry 16 false poly byte =
      CrcCanonicalWide.byteStep (CrcWidthEncoding.encode 16 poly) 0 byte := by
  change CrcWidthEncoding.encode 16 (CrcCanonicalWide.byteStep poly 0 byte) = _
  rw [CrcWidthEncoding.encode_byteStep hw hN]
  have hz : CrcWidthEncoding.encode 16 (0 : BitVec w) = 0 := by simp [CrcWidthEncoding.encode]
  rw [hz]

theorem entry_reflected {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 16) (poly : BitVec w) (byte : BitVec 8) :
    CrcPartialSpec.tableEntry 16 true poly byte =
      crc.polynomialRun (CrcWidthEncoding.encode 16 poly).reverse true 8 (byte.setWidth 16) := by
  change (CrcWidthEncoding.encode 16 (CrcReflectedWide.byteStep poly 0 byte)).reverse = _
  rw [CrcWidthEndpoints.encode_reflected_byteStep hw hN]
  have hz : CrcWidthEncoding.encode 16 (0 : BitVec w) = 0 := by simp [CrcWidthEncoding.encode]
  rw [hz, CrcReflectedWide.byteStep_injection (by decide)]
  apply congrArg (crc.polynomialRun (CrcWidthEncoding.encode 16 poly).reverse true 8)
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_reverse]

theorem new_table1 (a : CrcBody.crc_catalog.Algorithm U16) (poly : BitVec a.width.val)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 16) (hp : a.poly.bv = poly.setWidth 16) :
    ∃ self : CrcPublic16.Crc16, CrcBody.crc16.CrcU16Table.new 1#usize a = .ok self ∧
      self.algorithm = a ∧ CrcPartial16.TableCoherent a.refin poly self.data := by
  apply crc.total_result
  unfold CrcBody.crc16.CrcU16Table.new CrcBody.table.crc16_table
  simp only [show ¬(1#usize : Usize) > 1#usize by decide, ↓reduceIte]
  simp only [Aeneas.Std.bind_assoc, bind_ok]
  change WP.spec (do
    let pp ← CrcBody.crc16.init a a.poly
    let table ← CrcBody.table.crc16_table_loop0 a.refin pp
      (Array.repeat 1#usize (Array.repeat 256#usize 0#u16)) 0#usize
    .ok ({algorithm := a, data := table} : CrcPublic16.Crc16)) _
  rw [CrcPartial16.prepared_poly a poly hw hp]
  simp only [bind_ok]
  cases hr : a.refin with
  | false =>
    apply WP.spec_bind (CrcConstructor16.loop_spec
      (UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 poly))
      (Array.repeat 1#usize (Array.repeat 256#usize 0#u16)))
    intro table ht
    simp only [WP.spec_ok]
    refine ⟨True.intro, ?_⟩
    intro byte
    have hb : byte.val < 256 := by have h := byte.hmax; scalar_tac
    exact (ht byte hb).trans (entry_nonref hw.1 hw.2 poly byte.bv).symm
  | true =>
    apply WP.spec_bind (CrcReflectedConstructor16.loop_spec
      (UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 poly).reverse)
      (Array.repeat 1#usize (Array.repeat 256#usize 0#u16)))
    intro table ht
    simp only [WP.spec_ok]
    refine ⟨True.intro, ?_⟩
    intro byte
    have hb : byte.val < 256 := by have h := byte.hmax; scalar_tac
    exact (ht byte hb).trans (entry_reflected hw.1 hw.2 poly byte.bv).symm

theorem new_checksum (a : CrcBody.crc_catalog.Algorithm U16) (bytes : Slice U8)
    (poly initial xorout : BitVec a.width.val)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 16)
    (hp : a.poly.bv = poly.setWidth 16) (hi : a.init.bv = initial.setWidth 16)
    (hx : a.xorout.bv = xorout.setWidth 16) :
    ∃ self : CrcPublic16.Crc16, CrcBody.crc16.CrcU16Table.new 1#usize a = .ok self ∧
      ∃ out, CrcBody.crc16.CrcU16Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum a.refin a.refout poly initial xorout
        (bytes.val.map UScalar.bv)).setWidth 16 := by
  obtain ⟨self, hs, heq, ht⟩ := new_table1 a poly hw hp
  subst a
  exact ⟨self, hs, CrcPartial16.checksum_table1 self bytes poly initial xorout hw hp hi hx ht⟩

theorem new_protocol (a : CrcBody.crc_catalog.Algorithm U16) (initial : U16) (bytes : Slice U8)
    (poly xorout : BitVec a.width.val)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 16)
    (hp : a.poly.bv = poly.setWidth 16) (hx : a.xorout.bv = xorout.setWidth 16) :
    ∃ self : CrcPublic16.Crc16, CrcBody.crc16.CrcU16Table.new 1#usize a = .ok self ∧
      ∃ start final out,
      CrcBody.crc16.CrcU16Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc16.DigestAU16Table.update start bytes = .ok final ∧
      CrcBody.crc16.DigestAU16Table.finalize final = .ok out ∧
      out.bv = (CrcPartialSpec.checksum a.refin a.refout poly
        (initial.bv.setWidth a.width.val) xorout (bytes.val.map UScalar.bv)).setWidth 16 := by
  obtain ⟨self, hs, heq, ht⟩ := new_table1 a poly hw hp
  subst a
  exact ⟨self, hs, CrcPartial16.protocol_table1 self initial bytes poly xorout hw hp hx ht⟩

theorem empty_loop (reflect : Bool) (poly : U16) (table : Array (Array U16 256#usize) 0#usize) :
    WP.spec (CrcBody.table.crc16_table_loop0 reflect poly table 0#usize) (fun _ => True) := by
  unfold CrcBody.table.crc16_table_loop0
  apply loop.spec_decr_nat (measure := fun _ => 0) (inv := fun _ => True)
  · intro x _
    rcases x with ⟨t,i⟩
    unfold CrcBody.table.crc16_table_loop0.body
    simp only [show ¬(0#usize : Usize) > 0#usize by decide, ↓reduceIte, ite_self, WP.spec_ok]
  · trivial

theorem new_notable (a : CrcBody.crc_catalog.Algorithm U16) (poly : BitVec a.width.val)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 16) (hp : a.poly.bv = poly.setWidth 16) :
    ∃ self : CrcNoTable16.Crc16, CrcBody.crc16.CrcU16Table.new 0#usize a = .ok self ∧
      self.algorithm = a := by
  apply crc.total_result
  unfold CrcBody.crc16.CrcU16Table.new CrcBody.table.crc16_table
  simp only [show ¬(0#usize : Usize) > 1#usize by decide, ↓reduceIte, Aeneas.Std.bind_assoc, bind_ok]
  change WP.spec (do
    let pp ← CrcBody.crc16.init a a.poly
    let table ← CrcBody.table.crc16_table_loop0 a.refin pp
      (Array.repeat 0#usize (Array.repeat 256#usize 0#u16)) 0#usize
    .ok ({algorithm := a, data := table} : CrcNoTable16.Crc16)) _
  rw [CrcPartial16.prepared_poly a poly hw hp]
  simp only [bind_ok]
  apply WP.spec_bind (empty_loop a.refin
    (UScalar.mk (ty := .U16) (CrcPartialSpec.physical 16 a.refin poly))
    (Array.repeat 0#usize (Array.repeat 256#usize 0#u16)))
  intro table _
  simp only [WP.spec_ok]

theorem new_checksum_notable (a : CrcBody.crc_catalog.Algorithm U16) (bytes : Slice U8)
    (poly initial xorout : BitVec a.width.val)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 16)
    (hp : a.poly.bv = poly.setWidth 16) (hi : a.init.bv = initial.setWidth 16)
    (hx : a.xorout.bv = xorout.setWidth 16) :
    ∃ self : CrcNoTable16.Crc16, CrcBody.crc16.CrcU16Table.new 0#usize a = .ok self ∧
      ∃ out, CrcBody.crc16.CrcU16Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum a.refin a.refout poly initial xorout
        (bytes.val.map UScalar.bv)).setWidth 16 := by
  obtain ⟨self, hs, heq⟩ := new_notable a poly hw hp
  subst a
  exact ⟨self, hs, CrcPartial16.checksum_notable self bytes poly initial xorout hw hp hi hx⟩

theorem new_protocol_notable (a : CrcBody.crc_catalog.Algorithm U16) (initial : U16) (bytes : Slice U8)
    (poly xorout : BitVec a.width.val)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 16)
    (hp : a.poly.bv = poly.setWidth 16) (hx : a.xorout.bv = xorout.setWidth 16) :
    ∃ self : CrcNoTable16.Crc16, CrcBody.crc16.CrcU16Table.new 0#usize a = .ok self ∧
      ∃ start final out,
      CrcBody.crc16.CrcU16Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc16.DigestAU16Table.update start bytes = .ok final ∧
      CrcBody.crc16.DigestAU16Table.finalize final = .ok out ∧
      out.bv = (CrcPartialSpec.checksum a.refin a.refout poly
        (initial.bv.setWidth a.width.val) xorout (bytes.val.map UScalar.bv)).setWidth 16 := by
  obtain ⟨self, hs, heq⟩ := new_notable a poly hw hp
  subst a
  exact ⟨self, hs, CrcPartial16.protocol_notable self initial bytes poly xorout hw hp hx⟩
end CrcPartialConstructor16
