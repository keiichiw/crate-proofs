import Stage2Proofs.PartialSpec
import Stage2Proofs.FullWidth32
import Stage2Proofs.WordProtocols
open Aeneas Aeneas.Std Result
namespace CrcPartial32
abbrev Crc32 := CrcPublic32.Crc32
abbrev Digest32 := CrcPublic32.Digest32

def Coherent {w : Nat} (self : Crc32) (poly : BitVec w) : Prop :=
  ∀ byte : U8, (CrcPublic32.tableRead self.data byte).bv =
    CrcPartialSpec.tableEntry 32 self.algorithm.refin poly byte.bv

def auxiliary {w : Nat} (self : Crc32) (poly : BitVec w) : Crc32 :=
  {self with algorithm := {self.algorithm with poly := UScalar.mk (CrcWidthEncoding.encode 32 poly)}}

theorem coherent_nonref {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 32)
    (self : Crc32) (poly : BitVec w) (hr : self.algorithm.refin = false)
    (ht : Coherent self poly) : CrcPublic32.Coherent32 (auxiliary self poly) := by
  intro byte
  have h := ht byte
  simp only [Coherent, CrcPartialSpec.tableEntry, CrcPartialSpec.physical,
    CrcWidthEndpoints.storedEncode, CrcPartialSpec.byteStep, hr,
    Bool.false_eq_true, ↓reduceIte] at h
  change (CrcPublic32.tableRead self.data byte).bv =
    CrcCanonicalWide.byteStep (CrcWidthEncoding.encode 32 poly) 0 byte.bv
  exact h.trans (by simpa [CrcWidthEncoding.encode] using
    CrcWidthEncoding.encode_byteStep hw hN poly 0 byte.bv)

theorem coherent_reflected {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 32)
    (self : Crc32) (poly : BitVec w) (hr : self.algorithm.refin = true)
    (ht : Coherent self poly) : CrcReflectedTable32.Coherent (auxiliary self poly) := by
  intro byte
  have h := ht byte
  simp only [Coherent, CrcPartialSpec.tableEntry, CrcPartialSpec.physical,
    CrcWidthEndpoints.storedEncode, CrcPartialSpec.byteStep, hr, ↓reduceIte] at h
  change (CrcPublic32.tableRead self.data byte).bv =
    (CrcReflectedWide.byteStep (CrcWidthEncoding.encode 32 poly) 0 byte.bv).reverse
  exact h.trans (congrArg BitVec.reverse (by simpa [CrcWidthEncoding.encode] using
    CrcWidthEndpoints.encode_reflected_byteStep hw hN poly 0 byte.bv))

theorem update_table1 {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 32)
    (self : Crc32) (poly state : BitVec w) (value : U32) (bytes : Slice U8)
    (hs : value.bv = CrcPartialSpec.physical 32 self.algorithm.refin state)
    (ht : Coherent self poly) :
    ∃ out, CrcBody.crc32.CrcU32Table.update self value bytes = .ok out ∧
      out.bv = CrcPartialSpec.physical 32 self.algorithm.refin
        (CrcPartialSpec.run self.algorithm.refin poly state (bytes.val.map UScalar.bv)) := by
  cases hr : self.algorithm.refin
  · obtain ⟨out, ho, hv⟩ := CrcUpdate32.update_table_total self.algorithm self.data bytes value hr
    refine ⟨out, ho, ?_⟩
    have hm := CrcPublic32.run_canonical (auxiliary self poly)
      (coherent_nonref hw hN self poly hr ht) value bytes.val
    change (CrcUpdate32.run self.data value bytes.val).bv =
      CrcCanonicalWide.run (CrcWidthEncoding.encode 32 poly) value.bv
        (bytes.val.map UScalar.bv) at hm
    rw [hv, hm]
    simp only [CrcPartialSpec.physical, CrcWidthEndpoints.storedEncode, hr,
      Bool.false_eq_true, ↓reduceIte] at hs ⊢
    rw [hs]
    exact (CrcWidthEncoding.encode_run hw hN poly state _).symm
  · obtain ⟨out, ho, hv⟩ := CrcUpdate32Reflected.update_table_total self.algorithm self.data bytes value hr
    refine ⟨out, ho, ?_⟩
    have hm := CrcReflectedTable32.run_canonical (auxiliary self poly)
      (coherent_reflected hw hN self poly hr ht) value bytes.val
    change (CrcUpdate32Reflected.run self.data value bytes.val).bv =
      (CrcReflectedWide.run (CrcWidthEncoding.encode 32 poly) value.bv.reverse
        (bytes.val.map UScalar.bv)).reverse at hm
    rw [hv, hm]
    simp only [CrcPartialSpec.physical, CrcWidthEndpoints.storedEncode, hr, ↓reduceIte] at hs ⊢
    rw [hs, BitVec.reverse_reverse_eq]
    exact congrArg BitVec.reverse (CrcWidthEndpoints.encode_reflected_run hw hN poly state _).symm

/-- The configured polynomial is the bounded width-w polynomial, rather than only a low-bit proxy. -/
theorem digest_update_table1 (self : Digest32) (bytes : Slice U8)
    (poly state : BitVec self.crc.algorithm.width.val)
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 32)
    (_hp : self.crc.algorithm.poly.bv = poly.setWidth 32)
    (hs : self.value.bv = CrcPartialSpec.physical 32 self.crc.algorithm.refin state)
    (ht : Coherent self.crc poly) :
    ∃ out, CrcBody.crc32.DigestAU32Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv = CrcPartialSpec.physical 32 self.crc.algorithm.refin
        (CrcPartialSpec.run self.crc.algorithm.refin poly state (bytes.val.map UScalar.bv)) := by
  obtain ⟨out, ho, hv⟩ := update_table1 hw.1 hw.2 self.crc poly state self.value bytes hs ht
  exact ⟨{self with value := out}, by simp [CrcBody.crc32.DigestAU32Table.update, ho], rfl, hv⟩

theorem checksum_table1 (self : Crc32) (bytes : Slice U8)
    (poly xorout : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 32)
    (_hp : self.algorithm.poly.bv = poly.setWidth 32)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 32)
    (ht : Coherent self poly) :
    ∃ out, CrcBody.crc32.CrcU32Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout
        poly (self.algorithm.init.bv.setWidth self.algorithm.width.val) xorout
        (bytes.val.map UScalar.bv)).setWidth 32 := by
  obtain ⟨initial, hi, hib⟩ := CrcWidthEndpoints.init32_encoded self.algorithm self.algorithm.init hw
  obtain ⟨mid, hm, hmb⟩ := update_table1 hw.1 hw.2 self poly
    (self.algorithm.init.bv.setWidth self.algorithm.width.val) initial bytes hib ht
  generalize hstate : CrcPartialSpec.run self.algorithm.refin poly
    (self.algorithm.init.bv.setWidth self.algorithm.width.val) (bytes.val.map UScalar.bv) = finalState at hmb
  have hmb' : mid.bv = CrcWidthEndpoints.storedEncode 32 self.algorithm.refin finalState := hmb
  obtain ⟨out, ho, hob⟩ := CrcWidthEndpoints.finalize32_encoded self.algorithm mid xorout finalState hw hx hmb'
  refine ⟨out, ?_, ?_⟩
  · simp only [CrcBody.crc32.CrcU32Table.checksum, hi, hm, ho, bind_ok]
  · change out.bv = (CrcFullWidthSpec.finish self.algorithm.refout xorout
      (CrcPartialSpec.run self.algorithm.refin poly
        (self.algorithm.init.bv.setWidth self.algorithm.width.val) (bytes.val.map UScalar.bv))).setWidth 32
    rw [hstate]
    exact hob

abbrev NoCrc32 := CrcNoTable32.Crc32
abbrev NoDigest32 := CrcNoTable32.Digest32

theorem notable_fragment (self : NoCrc32) (value : U32) (bytes : Slice U8) :
    CrcBody.crc32.CrcU32Table.update self value bytes = (do
      let poly ← CrcBody.crc32.init self.algorithm self.algorithm.poly
      if self.algorithm.refin then
        CrcBody.crc32.update_table_loop7 value bytes (Slice.len bytes) 0#usize self.algorithm.refin poly
      else CrcBody.crc32.update_table_loop8 value bytes (Slice.len bytes) 0#usize self.algorithm.refin poly) := by
  unfold CrcBody.crc32.CrcU32Table.update CrcBody.crc32.update_table CrcBody.crc32.init
  simp only [show (0#usize : Usize) ≠ 16#usize by decide,
    show ¬(0#usize : Usize) > 0#usize by decide, ↓reduceIte]

theorem update_notable (self : NoCrc32)
    (poly state : BitVec self.algorithm.width.val) (value : U32) (bytes : Slice U8)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 32)
    (hp : self.algorithm.poly.bv = poly.setWidth 32)
    (hs : value.bv = CrcPartialSpec.physical 32 self.algorithm.refin state) :
    ∃ out, CrcBody.crc32.CrcU32Table.update self value bytes = .ok out ∧
      out.bv = CrcPartialSpec.physical 32 self.algorithm.refin
        (CrcPartialSpec.run self.algorithm.refin poly state (bytes.val.map UScalar.bv)) := by
  have hlow : self.algorithm.poly.bv.setWidth self.algorithm.width.val = poly := by
    rw [hp]
    simpa using BitVec.setWidth_setWidth_of_le poly hw.2
  have hprep := CrcWidthEndpoints.init32_eq_encoded self.algorithm self.algorithm.poly hw
  rw [hlow] at hprep
  cases hr : self.algorithm.refin
  · let pp : U32 := UScalar.mk (CrcWidthEncoding.encode 32 poly)
    obtain ⟨out, ho, hv⟩ := crc.total_result (CrcNoTable32.loop_spec pp bytes value)
    refine ⟨out, ?_, ?_⟩
    · simp only [notable_fragment, hprep, bind_ok, hr, Bool.false_eq_true, ↓reduceIte,
        CrcWidthEndpoints.storedEncode]
      exact ho
    · have hm := CrcNoTable32.run_bv pp value bytes.val
      change (CrcNoTable32.run pp value bytes.val).bv =
        CrcCanonicalWide.run (CrcWidthEncoding.encode 32 poly) value.bv
          (bytes.val.map UScalar.bv) at hm
      rw [hv, hm]
      simp only [CrcPartialSpec.physical, CrcWidthEndpoints.storedEncode, hr,
        Bool.false_eq_true, ↓reduceIte] at hs ⊢
      rw [hs]
      exact (CrcWidthEncoding.encode_run hw.1 hw.2 poly state _).symm
  · let pp : U32 := UScalar.mk (CrcWidthEncoding.encode 32 poly)
    obtain ⟨out, ho, hv⟩ := crc.total_result
      (CrcReflectedNoTable32.loop_spec (CrcReflectedPublic32.reverseScalar pp) bytes value)
    refine ⟨out, ?_, ?_⟩
    · simp only [notable_fragment, hprep, bind_ok, hr, ↓reduceIte,
        CrcWidthEndpoints.storedEncode]
      exact ho
    · have hm := congrArg BitVec.reverse (CrcReflectedNoTable32.run_decoded pp value bytes.val)
      simp only [BitVec.reverse_reverse_eq] at hm
      change (CrcReflectedNoTable32.run (CrcReflectedPublic32.reverseScalar pp) value bytes.val).bv =
        (CrcReflectedWide.run (CrcWidthEncoding.encode 32 poly) value.bv.reverse
          (bytes.val.map UScalar.bv)).reverse at hm
      rw [hv, hm]
      simp only [CrcPartialSpec.physical, CrcWidthEndpoints.storedEncode, hr, ↓reduceIte] at hs ⊢
      rw [hs, BitVec.reverse_reverse_eq]
      exact congrArg BitVec.reverse (CrcWidthEndpoints.encode_reflected_run hw.1 hw.2 poly state _).symm

theorem digest_update_notable (self : NoDigest32) (bytes : Slice U8)
    (poly state : BitVec self.crc.algorithm.width.val)
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 32)
    (hp : self.crc.algorithm.poly.bv = poly.setWidth 32)
    (hs : self.value.bv = CrcPartialSpec.physical 32 self.crc.algorithm.refin state) :
    ∃ out, CrcBody.crc32.DigestAU32Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv = CrcPartialSpec.physical 32 self.crc.algorithm.refin
        (CrcPartialSpec.run self.crc.algorithm.refin poly state (bytes.val.map UScalar.bv)) := by
  obtain ⟨out, ho, hv⟩ := update_notable self.crc poly state self.value bytes hw hp hs
  exact ⟨{self with value := out}, by simp [CrcBody.crc32.DigestAU32Table.update, ho], rfl, hv⟩

theorem checksum_notable (self : NoCrc32) (bytes : Slice U8)
    (poly xorout : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 32)
    (hp : self.algorithm.poly.bv = poly.setWidth 32)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 32) :
    ∃ out, CrcBody.crc32.CrcU32Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout
        poly (self.algorithm.init.bv.setWidth self.algorithm.width.val) xorout
        (bytes.val.map UScalar.bv)).setWidth 32 := by
  obtain ⟨initial, hi, hib⟩ := CrcWidthEndpoints.init32_encoded self.algorithm self.algorithm.init hw
  obtain ⟨mid, hm, hmb⟩ := update_notable self poly
    (self.algorithm.init.bv.setWidth self.algorithm.width.val) initial bytes hw hp hib
  generalize hstate : CrcPartialSpec.run self.algorithm.refin poly
    (self.algorithm.init.bv.setWidth self.algorithm.width.val) (bytes.val.map UScalar.bv) = finalState at hmb
  have hmb' : mid.bv = CrcWidthEndpoints.storedEncode 32 self.algorithm.refin finalState := hmb
  obtain ⟨out, ho, hob⟩ := CrcWidthEndpoints.finalize32_encoded self.algorithm mid xorout finalState hw hx hmb'
  refine ⟨out, ?_, ?_⟩
  · simp only [CrcBody.crc32.CrcU32Table.checksum, hi, hm, ho, bind_ok]
  · change out.bv = (CrcFullWidthSpec.finish self.algorithm.refout xorout
      (CrcPartialSpec.run self.algorithm.refin poly
        (self.algorithm.init.bv.setWidth self.algorithm.width.val) (bytes.val.map UScalar.bv))).setWidth 32
    rw [hstate]
    exact hob

end CrcPartial32
