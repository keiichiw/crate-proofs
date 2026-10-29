import Stage2Proofs.PartialSpec
import Stage2Proofs.FullWidth128
import Stage2Proofs.WordProtocols
open Aeneas Aeneas.Std Result
namespace CrcPartial128
abbrev Crc128 := CrcPublic128.Crc128
abbrev Digest128 := CrcPublic128.Digest128

def Coherent {w : Nat} (self : Crc128) (poly : BitVec w) : Prop :=
  ∀ byte : U8, (CrcPublic128.tableRead self.data byte).bv =
    CrcPartialSpec.tableEntry 128 self.algorithm.refin poly byte.bv

def auxiliary {w : Nat} (self : Crc128) (poly : BitVec w) : Crc128 :=
  {self with algorithm := {self.algorithm with poly := UScalar.mk (CrcWidthEncoding.encode 128 poly)}}

theorem coherent_nonref {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 128)
    (self : Crc128) (poly : BitVec w) (hr : self.algorithm.refin = false)
    (ht : Coherent self poly) : CrcPublic128.Coherent128 (auxiliary self poly) := by
  intro byte
  have h := ht byte
  simp only [CrcPartialSpec.tableEntry, CrcPartialSpec.physical,
    CrcWidthEndpoints.storedEncode, CrcPartialSpec.byteStep, hr,
    Bool.false_eq_true, ↓reduceIte] at h
  change (CrcPublic128.tableRead self.data byte).bv =
    CrcCanonicalWide.byteStep (CrcWidthEncoding.encode 128 poly) 0 byte.bv
  exact h.trans (by simpa [CrcWidthEncoding.encode] using
    CrcWidthEncoding.encode_byteStep hw hN poly 0 byte.bv)

theorem coherent_reflected {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 128)
    (self : Crc128) (poly : BitVec w) (hr : self.algorithm.refin = true)
    (ht : Coherent self poly) : CrcReflectedTable128.Coherent (auxiliary self poly) := by
  intro byte
  have h := ht byte
  simp only [CrcPartialSpec.tableEntry, CrcPartialSpec.physical,
    CrcWidthEndpoints.storedEncode, CrcPartialSpec.byteStep, hr, ↓reduceIte] at h
  change (CrcPublic128.tableRead self.data byte).bv =
    (CrcReflectedWide.byteStep (CrcWidthEncoding.encode 128 poly) 0 byte.bv).reverse
  exact h.trans (congrArg BitVec.reverse (by simpa [CrcWidthEncoding.encode] using
    CrcWidthEndpoints.encode_reflected_byteStep hw hN poly 0 byte.bv))

theorem update_table1 {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 128)
    (self : Crc128) (poly state : BitVec w) (value : U128) (bytes : Slice U8)
    (hs : value.bv = CrcPartialSpec.physical 128 self.algorithm.refin state)
    (ht : Coherent self poly) :
    ∃ out, CrcBody.crc128.CrcU128Table.update self value bytes = .ok out ∧
      out.bv = CrcPartialSpec.physical 128 self.algorithm.refin
        (CrcPartialSpec.run self.algorithm.refin poly state (bytes.val.map UScalar.bv)) := by
  cases hr : self.algorithm.refin
  · obtain ⟨out, ho, hv⟩ := CrcUpdate128.update_table_total self.algorithm self.data bytes value hr
    refine ⟨out, ho, ?_⟩
    have hm := CrcPublic128.run_canonical (auxiliary self poly)
      (coherent_nonref hw hN self poly hr ht) value bytes.val
    change (CrcUpdate128.run self.data value bytes.val).bv =
      CrcCanonicalWide.run (CrcWidthEncoding.encode 128 poly) value.bv
        (bytes.val.map UScalar.bv) at hm
    rw [hv, hm]
    simp only [CrcPartialSpec.physical, CrcWidthEndpoints.storedEncode, hr,
      Bool.false_eq_true, ↓reduceIte] at hs ⊢
    rw [hs]
    exact (CrcWidthEncoding.encode_run hw hN poly state _).symm
  · obtain ⟨out, ho, hv⟩ := CrcUpdate128Reflected.update_table_total self.algorithm self.data bytes value hr
    refine ⟨out, ho, ?_⟩
    have hm := CrcReflectedTable128.run_canonical (auxiliary self poly)
      (coherent_reflected hw hN self poly hr ht) value bytes.val
    change (CrcUpdate128Reflected.run self.data value bytes.val).bv =
      (CrcReflectedWide.run (CrcWidthEncoding.encode 128 poly) value.bv.reverse
        (bytes.val.map UScalar.bv)).reverse at hm
    rw [hv, hm]
    simp only [CrcPartialSpec.physical, CrcWidthEndpoints.storedEncode, hr, ↓reduceIte] at hs ⊢
    rw [hs, BitVec.reverse_reverse_eq]
    exact congrArg BitVec.reverse (CrcWidthEndpoints.encode_reflected_run hw hN poly state _).symm

/-- The configured polynomial is the bounded width-w polynomial, rather than only a low-bit proxy. -/
theorem digest_update_table1 (self : Digest128) (bytes : Slice U8)
    (poly state : BitVec self.crc.algorithm.width.val)
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 128)
    (_hp : self.crc.algorithm.poly.bv = poly.setWidth 128)
    (hs : self.value.bv = CrcPartialSpec.physical 128 self.crc.algorithm.refin state)
    (ht : Coherent self.crc poly) :
    ∃ out, CrcBody.crc128.DigestAU128Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv = CrcPartialSpec.physical 128 self.crc.algorithm.refin
        (CrcPartialSpec.run self.crc.algorithm.refin poly state (bytes.val.map UScalar.bv)) := by
  obtain ⟨out, ho, hv⟩ := update_table1 hw.1 hw.2 self.crc poly state self.value bytes hs ht
  exact ⟨{self with value := out}, by simp [CrcBody.crc128.DigestAU128Table.update, ho], rfl, hv⟩

theorem checksum_table1 (self : Crc128) (bytes : Slice U8)
    (poly xorout : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 128)
    (_hp : self.algorithm.poly.bv = poly.setWidth 128)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 128)
    (ht : Coherent self poly) :
    ∃ out, CrcBody.crc128.CrcU128Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout
        poly (self.algorithm.init.bv.setWidth self.algorithm.width.val) xorout
        (bytes.val.map UScalar.bv)).setWidth 128 := by
  obtain ⟨initial, hi, hib⟩ := CrcWidthEndpoints.init128_encoded self.algorithm self.algorithm.init hw
  obtain ⟨mid, hm, hmb⟩ := update_table1 hw.1 hw.2 self poly
    (self.algorithm.init.bv.setWidth self.algorithm.width.val) initial bytes hib ht
  generalize hstate : CrcPartialSpec.run self.algorithm.refin poly
    (self.algorithm.init.bv.setWidth self.algorithm.width.val) (bytes.val.map UScalar.bv) = finalState at hmb
  have hmb' : mid.bv = CrcWidthEndpoints.storedEncode 128 self.algorithm.refin finalState := hmb
  obtain ⟨out, ho, hob⟩ := CrcWidthEndpoints.finalize128_encoded self.algorithm mid xorout finalState hw hx hmb'
  refine ⟨out, ?_, ?_⟩
  · simp only [CrcBody.crc128.CrcU128Table.checksum, hi, hm, ho, bind_ok]
  · change out.bv = (CrcFullWidthSpec.finish self.algorithm.refout xorout
      (CrcPartialSpec.run self.algorithm.refin poly
        (self.algorithm.init.bv.setWidth self.algorithm.width.val) (bytes.val.map UScalar.bv))).setWidth 128
    rw [hstate]
    exact hob


theorem update_notable (self : CrcNoTable128.Crc128)
    (poly state : BitVec self.algorithm.width.val) (value : U128) (bytes : Slice U8)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 128)
    (hp : self.algorithm.poly.bv = poly.setWidth 128)
    (hs : value.bv = CrcPartialSpec.physical 128 self.algorithm.refin state) :
    ∃ out, CrcBody.crc128.CrcU128Table.update self value bytes = .ok out ∧
      out.bv = CrcPartialSpec.physical 128 self.algorithm.refin
        (CrcPartialSpec.run self.algorithm.refin poly state (bytes.val.map UScalar.bv)) := by
  have hpLow : self.algorithm.poly.bv.setWidth self.algorithm.width.val = poly := by
    rw [hp]
    simpa using BitVec.setWidth_setWidth_of_le poly hw.2
  have hi := CrcWidthEndpoints.init128_eq_encoded self.algorithm self.algorithm.poly hw
  rw [hpLow] at hi
  cases hr : self.algorithm.refin
  · simp only [CrcWidthEndpoints.storedEncode, hr, Bool.false_eq_true, ↓reduceIte] at hi
    obtain ⟨out,ho,hv⟩ := crc.total_result (CrcNoTable128.loop_spec
      (UScalar.mk (CrcWidthEncoding.encode 128 poly)) bytes value)
    refine ⟨out,?_,?_⟩
    · unfold CrcBody.crc128.CrcU128Table.update CrcBody.crc128.update_table
      simp only [show (0#usize : Usize) ≠ 16#usize by decide, ↓reduceIte,
        show ¬(0#usize : Usize) > 0#usize by decide, hr, Bool.false_eq_true]
      simp only [CrcBody.crc128.init,hr,Bool.false_eq_true,↓reduceIte] at hi
      rw [hi]
      simpa only [bind_ok] using ho
    · rw [hv, CrcNoTable128.run_bv]
      simp only [CrcPartialSpec.physical,CrcWidthEndpoints.storedEncode,hr,
        Bool.false_eq_true,↓reduceIte] at hs ⊢
      rw [hs]
      exact (CrcWidthEncoding.encode_run hw.1 hw.2 poly state _).symm
  · simp only [CrcWidthEndpoints.storedEncode, hr, ↓reduceIte] at hi
    obtain ⟨out,ho,hv⟩ := crc.total_result (CrcReflectedNoTable128.loop_spec
      (UScalar.mk (CrcWidthEncoding.encode 128 poly).reverse) bytes value)
    refine ⟨out,?_,?_⟩
    · unfold CrcBody.crc128.CrcU128Table.update CrcBody.crc128.update_table
      simp only [show (0#usize : Usize) ≠ 16#usize by decide, ↓reduceIte,
        show ¬(0#usize : Usize) > 0#usize by decide, hr]
      simp only [CrcBody.crc128.init,hr,↓reduceIte] at hi
      rw [hi]
      simpa only [bind_ok] using ho
    · have hb := CrcReflectedNoTable128.run_decoded
        (UScalar.mk (CrcWidthEncoding.encode 128 poly)) value bytes.val
      change (CrcReflectedNoTable128.run (UScalar.mk (CrcWidthEncoding.encode 128 poly).reverse)
        value bytes.val).bv.reverse = CrcReflectedWide.run (CrcWidthEncoding.encode 128 poly)
        value.bv.reverse (bytes.val.map UScalar.bv) at hb
      rw [hv]
      simp only [CrcPartialSpec.physical,CrcWidthEndpoints.storedEncode,hr,↓reduceIte] at hs ⊢
      rw [hs,BitVec.reverse_reverse_eq] at hb
      have henc := CrcWidthEndpoints.encode_reflected_run hw.1 hw.2 poly state (bytes.val.map UScalar.bv)
      have hx := congrArg BitVec.reverse (hb.trans henc.symm)
      simpa only [BitVec.reverse_reverse_eq, CrcPartialSpec.run, CrcFullWidthSpec.run, ↓reduceIte] using hx

theorem digest_update_notable (self : CrcNoTable128.Digest128) (bytes : Slice U8)
    (poly state : BitVec self.crc.algorithm.width.val)
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 128)
    (hp : self.crc.algorithm.poly.bv = poly.setWidth 128)
    (hs : self.value.bv = CrcPartialSpec.physical 128 self.crc.algorithm.refin state)
    :
    ∃ out, CrcBody.crc128.DigestAU128Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv = CrcPartialSpec.physical 128 self.crc.algorithm.refin
        (CrcPartialSpec.run self.crc.algorithm.refin poly state (bytes.val.map UScalar.bv)) := by
  obtain ⟨out, ho, hv⟩ := update_notable self.crc poly state self.value bytes hw hp hs
  exact ⟨{self with value := out}, by simp [CrcBody.crc128.DigestAU128Table.update, ho], rfl, hv⟩

theorem checksum_notable (self : CrcNoTable128.Crc128) (bytes : Slice U8)
    (poly xorout : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 128)
    (hp : self.algorithm.poly.bv = poly.setWidth 128)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 128)
    :
    ∃ out, CrcBody.crc128.CrcU128Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout
        poly (self.algorithm.init.bv.setWidth self.algorithm.width.val) xorout
        (bytes.val.map UScalar.bv)).setWidth 128 := by
  obtain ⟨initial, hi, hib⟩ := CrcWidthEndpoints.init128_encoded self.algorithm self.algorithm.init hw
  obtain ⟨mid, hm, hmb⟩ := update_notable self poly
    (self.algorithm.init.bv.setWidth self.algorithm.width.val) initial bytes hw hp hib
  generalize hstate : CrcPartialSpec.run self.algorithm.refin poly
    (self.algorithm.init.bv.setWidth self.algorithm.width.val) (bytes.val.map UScalar.bv) = finalState at hmb
  have hmb' : mid.bv = CrcWidthEndpoints.storedEncode 128 self.algorithm.refin finalState := hmb
  obtain ⟨out, ho, hob⟩ := CrcWidthEndpoints.finalize128_encoded self.algorithm mid xorout finalState hw hx hmb'
  refine ⟨out, ?_, ?_⟩
  · simp only [CrcBody.crc128.CrcU128Table.checksum, hi, hm, ho, bind_ok]
  · change out.bv = (CrcFullWidthSpec.finish self.algorithm.refout xorout
      (CrcPartialSpec.run self.algorithm.refin poly
        (self.algorithm.init.bv.setWidth self.algorithm.width.val) (bytes.val.map UScalar.bv))).setWidth 128
    rw [hstate]
    exact hob


end CrcPartial128
