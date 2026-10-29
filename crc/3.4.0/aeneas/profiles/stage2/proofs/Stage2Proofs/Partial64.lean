import Stage2Proofs.FullWidth64
import Stage2Proofs.WidthEncoding
import Stage2Proofs.WidthEndpoints
import Stage2Proofs.PartialSpec
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
namespace CrcPartial64

/-- The table's mathematical polynomial is the width-aligned physical word. -/
def withPoly {w : Nat} (self : CrcPublic64.Crc64) (poly : BitVec w) : CrcPublic64.Crc64 :=
  {self with algorithm := {self.algorithm with poly := UScalar.mk (ty := .U64) (CrcWidthEncoding.encode 64 poly)}}

def Coherent {w : Nat} (self : CrcPublic64.Crc64) (poly : BitVec w) : Prop :=
  CrcFullWidth64.Coherent (withPoly self poly)

theorem update_table1_nonref {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 64)
    (self : CrcPublic64.Crc64) (poly state : BitVec w) (bytes : Slice U8)
    (hr : self.algorithm.refin = false) (ht : Coherent self poly) :
    ∃ out, CrcBody.crc64.CrcU64Table.update self
      (UScalar.mk (ty := .U64) (CrcWidthEncoding.encode 64 state)) bytes = .ok out ∧
      out.bv = CrcWidthEncoding.encode 64
        (CrcCanonicalWide.run poly state (bytes.val.map UScalar.bv)) := by
  obtain ⟨out,ho,hv⟩ := CrcUpdate64.update_table_total self.algorithm self.data bytes
    (UScalar.mk (ty := .U64) (CrcWidthEncoding.encode 64 state)) hr
  have hc : CrcPublic64.Coherent64 (withPoly self poly) := by
    simpa only [Coherent,CrcFullWidth64.Coherent,withPoly,hr,Bool.false_eq_true,↓reduceIte] using ht
  have hm := CrcPublic64.run_canonical (withPoly self poly) hc
    (UScalar.mk (ty := .U64) (CrcWidthEncoding.encode 64 state)) bytes.val
  refine ⟨out,ho,?_⟩
  exact (congrArg UScalar.bv hv).trans (hm.trans (CrcWidthEncoding.encode_run hw hN poly state _).symm)
theorem update_table1_reflected {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 64)
    (self : CrcPublic64.Crc64) (poly state : BitVec w) (bytes : Slice U8)
    (hr : self.algorithm.refin = true) (ht : Coherent self poly) :
    ∃ out, CrcBody.crc64.CrcU64Table.update self
      (UScalar.mk (ty := .U64) (CrcWidthEndpoints.storedEncode 64 true state)) bytes = .ok out ∧
      out.bv = CrcWidthEndpoints.storedEncode 64 true
        (CrcReflectedWide.run poly state (bytes.val.map UScalar.bv)) := by
  obtain ⟨out,ho,hv⟩ := CrcUpdate64Reflected.update_table_total self.algorithm self.data bytes
    (UScalar.mk (ty := .U64) (CrcWidthEndpoints.storedEncode 64 true state)) hr
  have hc : CrcReflectedTable64.Coherent (withPoly self poly) := by
    simpa only [Coherent,CrcFullWidth64.Coherent,withPoly,hr,↓reduceIte] using ht
  have hm := CrcReflectedTable64.run_canonical (withPoly self poly) hc
    (UScalar.mk (ty := .U64) (CrcWidthEndpoints.storedEncode 64 true state)) bytes.val
  refine ⟨out,ho,?_⟩
  change (CrcUpdate64Reflected.run self.data
      (UScalar.mk (ty := .U64) (CrcWidthEndpoints.storedEncode 64 true state)) bytes.val).bv =
      (CrcReflectedWide.run (CrcWidthEncoding.encode 64 poly)
        (CrcWidthEncoding.encode 64 state).reverse.reverse (bytes.val.map UScalar.bv)).reverse at hm
  rw [BitVec.reverse_reverse_eq] at hm
  have hm' := hm
  exact (congrArg UScalar.bv hv).trans (hm'.trans
    (congrArg BitVec.reverse (CrcWidthEndpoints.encode_reflected_run hw hN poly state _).symm))

theorem update_table1 {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 64)
    (self : CrcPublic64.Crc64) (poly state : BitVec w) (bytes : Slice U8)
    (ht : Coherent self poly) :
    ∃ out, CrcBody.crc64.CrcU64Table.update self
      (UScalar.mk (ty := .U64) (CrcWidthEndpoints.storedEncode 64 self.algorithm.refin state)) bytes = .ok out ∧
      out.bv = CrcWidthEndpoints.storedEncode 64 self.algorithm.refin
        (CrcFullWidthSpec.run self.algorithm.refin poly state (bytes.val.map UScalar.bv)) := by
  cases hr : self.algorithm.refin
  · simpa only [hr,CrcWidthEndpoints.storedEncode,CrcFullWidthSpec.run,Bool.false_eq_true,↓reduceIte]
      using update_table1_nonref hw hN self poly state bytes hr ht
  · simpa only [hr,CrcFullWidthSpec.run,↓reduceIte]
      using update_table1_reflected hw hN self poly state bytes hr ht
def physicalRun {w : Nat} (refin : Bool) (poly : BitVec w) (state : U64)
    (bytes : List U8) : U64 :=
  if refin then CrcReflectedNoTable64.run
    (CrcReflectedPublic64.reverseScalar (UScalar.mk (ty := .U64) (CrcWidthEncoding.encode 64 poly))) state bytes
  else CrcNoTable64.run (UScalar.mk (ty := .U64) (CrcWidthEncoding.encode 64 poly)) state bytes

theorem update_notable_raw (self : CrcNoTable64.Crc64)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 64)
    (poly : BitVec self.algorithm.width.val) (hp : self.algorithm.poly.bv = poly.setWidth 64)
    (state : U64) (bytes : Slice U8) :
    ∃ out, CrcBody.crc64.CrcU64Table.update self state bytes = .ok out ∧
      out = physicalRun self.algorithm.refin poly state bytes.val := by
  obtain ⟨pp,hpp,henc⟩ := CrcWidthEndpoints.init64_encoded self.algorithm self.algorithm.poly hw
  have he : pp.bv = CrcWidthEndpoints.storedEncode 64 self.algorithm.refin poly := by
    simpa only [hp, BitVec.setWidth_setWidth_of_le _ hw.2, BitVec.setWidth_eq] using henc
  have hpp' : pp = UScalar.mk (ty := .U64) (CrcWidthEndpoints.storedEncode 64 self.algorithm.refin poly) :=
    (UScalar.eq_equiv_bv_eq _ _).mpr he
  apply crc.total_result
  unfold CrcBody.crc64.CrcU64Table.update CrcBody.crc64.update_table
  simp only [show (0#usize : Usize) ≠ 16#usize by decide, ↓reduceIte,
    show ¬(0#usize : Usize) > 0#usize by decide]
  change WP.spec (do
    let pp ← CrcBody.crc64.init self.algorithm self.algorithm.poly
    if self.algorithm.refin then CrcBody.crc64.update_table_loop7 state bytes (Slice.len bytes) 0#usize self.algorithm.refin pp
    else CrcBody.crc64.update_table_loop8 state bytes (Slice.len bytes) 0#usize self.algorithm.refin pp)
    (fun out => out = physicalRun self.algorithm.refin poly state bytes.val)
  rw [hpp, hpp']
  simp only [bind_ok]
  cases hr : self.algorithm.refin
  · simpa only [physicalRun,CrcWidthEndpoints.storedEncode,Bool.false_eq_true,↓reduceIte] using CrcNoTable64.loop_spec (UScalar.mk (ty := .U64) (CrcWidthEncoding.encode 64 poly)) bytes state
  · simpa only [physicalRun,CrcWidthEndpoints.storedEncode,CrcReflectedPublic64.reverseScalar,U64.bv,UScalar.bv_mk,↓reduceIte] using CrcReflectedNoTable64.loop_spec (UScalar.mk (ty := .U64) (CrcWidthEndpoints.storedEncode 64 true poly)) bytes state
theorem physicalRun_encoded {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 64)
    (refin : Bool) (poly state : BitVec w) (bytes : List U8) :
    (physicalRun refin poly (UScalar.mk (ty := .U64) (CrcPartialSpec.physical 64 refin state)) bytes).bv =
      CrcPartialSpec.physical 64 refin (CrcPartialSpec.run refin poly state (bytes.map UScalar.bv)) := by
  cases refin
  · exact (CrcNoTable64.run_bv (UScalar.mk (ty := .U64) (CrcWidthEncoding.encode 64 poly))
      (UScalar.mk (ty := .U64) (CrcWidthEncoding.encode 64 state)) bytes).trans
      (CrcWidthEncoding.encode_run hw hN poly state _).symm
  · have h := CrcReflectedNoTable64.run_decoded (UScalar.mk (ty := .U64) (CrcWidthEncoding.encode 64 poly))
      (UScalar.mk (ty := .U64) (CrcPartialSpec.physical 64 true state)) bytes
    change (physicalRun true poly (UScalar.mk (ty := .U64) (CrcPartialSpec.physical 64 true state)) bytes).bv.reverse =
      CrcReflectedWide.run (CrcWidthEncoding.encode 64 poly)
        (CrcWidthEncoding.encode 64 state).reverse.reverse (bytes.map UScalar.bv) at h
    rw [BitVec.reverse_reverse_eq] at h
    have h' := h.trans (CrcWidthEndpoints.encode_reflected_run hw hN poly state _).symm
    simpa only [BitVec.reverse_reverse_eq,CrcPartialSpec.physical,CrcWidthEndpoints.storedEncode,
      CrcPartialSpec.run,CrcFullWidthSpec.run,↓reduceIte] using congrArg BitVec.reverse h'

theorem update_notable (self : CrcNoTable64.Crc64)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 64)
    (poly state : BitVec self.algorithm.width.val)
    (hp : self.algorithm.poly.bv = poly.setWidth 64) (bytes : Slice U8) :
    ∃ out, CrcBody.crc64.CrcU64Table.update self
      (UScalar.mk (ty := .U64) (CrcPartialSpec.physical 64 self.algorithm.refin state)) bytes = .ok out ∧
      out.bv = CrcPartialSpec.physical 64 self.algorithm.refin
        (CrcPartialSpec.run self.algorithm.refin poly state (bytes.val.map UScalar.bv)) := by
  obtain ⟨out,ho,hv⟩ := update_notable_raw self hw poly hp
    (UScalar.mk (ty := .U64) (CrcPartialSpec.physical 64 self.algorithm.refin state)) bytes
  exact ⟨out,ho,(congrArg UScalar.bv hv).trans (physicalRun_encoded hw.1 hw.2 _ _ _ _)⟩
theorem checksum_notable (self : CrcNoTable64.Crc64)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 64)
    (poly xorout : BitVec self.algorithm.width.val)
    (hp : self.algorithm.poly.bv = poly.setWidth 64)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 64) (bytes : Slice U8) :
    ∃ out, CrcBody.crc64.CrcU64Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout poly
        (self.algorithm.init.bv.setWidth self.algorithm.width.val) xorout
        (bytes.val.map UScalar.bv)).setWidth 64 := by
  obtain ⟨mid,hm,hstate⟩ := update_notable self hw poly
    (self.algorithm.init.bv.setWidth self.algorithm.width.val) hp bytes
  generalize hcanon : CrcPartialSpec.run self.algorithm.refin poly
    (self.algorithm.init.bv.setWidth self.algorithm.width.val) (bytes.val.map UScalar.bv) = finalState at hstate
  have hstate' : mid.bv = CrcWidthEndpoints.storedEncode 64 self.algorithm.refin finalState := by
    first
    | exact hstate
    | rw [← hcanon]; exact hstate
  obtain ⟨out,ho,hv⟩ := CrcWidthEndpoints.finalize64_encoded self.algorithm mid xorout finalState hw hx hstate' 
  refine ⟨out,?_,?_⟩
  · simp only [CrcBody.crc64.CrcU64Table.checksum,
      CrcWidthEndpoints.init64_eq_encoded _ _ hw,hm,ho,bind_ok]
  · change out.bv = ((if self.algorithm.refout then
      (CrcPartialSpec.run self.algorithm.refin poly
        (self.algorithm.init.bv.setWidth self.algorithm.width.val) (bytes.val.map UScalar.bv)).reverse else
      CrcPartialSpec.run self.algorithm.refin poly
        (self.algorithm.init.bv.setWidth self.algorithm.width.val) (bytes.val.map UScalar.bv)) ^^^ xorout).setWidth 64
    rw [hcanon]
    exact hv

theorem checksum_table1 (self : CrcPublic64.Crc64)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 64)
    (poly xorout : BitVec self.algorithm.width.val)
    (_hp : self.algorithm.poly.bv = poly.setWidth 64)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 64)
    (ht : Coherent self poly) (bytes : Slice U8) :
    ∃ out, CrcBody.crc64.CrcU64Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout poly
        (self.algorithm.init.bv.setWidth self.algorithm.width.val) xorout
        (bytes.val.map UScalar.bv)).setWidth 64 := by
  obtain ⟨mid,hm,hstate⟩ := update_table1 hw.1 hw.2 self poly
    (self.algorithm.init.bv.setWidth self.algorithm.width.val) bytes ht
  generalize hcanon : CrcPartialSpec.run self.algorithm.refin poly
    (self.algorithm.init.bv.setWidth self.algorithm.width.val) (bytes.val.map UScalar.bv) = finalState at hstate
  have hstate' : mid.bv = CrcWidthEndpoints.storedEncode 64 self.algorithm.refin finalState := by
    first
    | exact hstate
    | rw [← hcanon]; exact hstate
  obtain ⟨out,ho,hv⟩ := CrcWidthEndpoints.finalize64_encoded self.algorithm mid xorout finalState hw hx hstate' 
  refine ⟨out,?_,?_⟩
  · simp only [CrcBody.crc64.CrcU64Table.checksum,
      CrcWidthEndpoints.init64_eq_encoded _ _ hw,hm,ho,bind_ok]
  · change out.bv = ((if self.algorithm.refout then
      (CrcPartialSpec.run self.algorithm.refin poly
        (self.algorithm.init.bv.setWidth self.algorithm.width.val) (bytes.val.map UScalar.bv)).reverse else
      CrcPartialSpec.run self.algorithm.refin poly
        (self.algorithm.init.bv.setWidth self.algorithm.width.val) (bytes.val.map UScalar.bv)) ^^^ xorout).setWidth 64
    rw [hcanon]
    exact hv
theorem digest_update_table1 (self : CrcPublic64.Digest64)
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 64)
    (poly state : BitVec self.crc.algorithm.width.val)
    (_hp : self.crc.algorithm.poly.bv = poly.setWidth 64)
    (ht : Coherent self.crc poly)
    (hs : self.value.bv = CrcPartialSpec.physical 64 self.crc.algorithm.refin state)
    (bytes : Slice U8) :
    ∃ out, CrcBody.crc64.DigestAU64Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv = CrcPartialSpec.physical 64 self.crc.algorithm.refin
        (CrcPartialSpec.run self.crc.algorithm.refin poly state (bytes.val.map UScalar.bv)) := by
  obtain ⟨mid,hm,hv⟩ := update_table1 hw.1 hw.2 self.crc poly state bytes ht
  have he : self.value = UScalar.mk (ty := .U64) (CrcPartialSpec.physical 64 self.crc.algorithm.refin state) :=
    (UScalar.eq_equiv_bv_eq _ _).mpr hs
  refine ⟨{self with value := mid},?_,rfl,hv⟩
  simp only [CrcBody.crc64.DigestAU64Table.update,he,hm,bind_ok]

theorem digest_update_notable (self : CrcNoTable64.Digest64)
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 64)
    (poly state : BitVec self.crc.algorithm.width.val)
    (hp : self.crc.algorithm.poly.bv = poly.setWidth 64)
    (hs : self.value.bv = CrcPartialSpec.physical 64 self.crc.algorithm.refin state)
    (bytes : Slice U8) :
    ∃ out, CrcBody.crc64.DigestAU64Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv = CrcPartialSpec.physical 64 self.crc.algorithm.refin
        (CrcPartialSpec.run self.crc.algorithm.refin poly state (bytes.val.map UScalar.bv)) := by
  obtain ⟨mid,hm,hv⟩ := update_notable self.crc hw poly state hp bytes
  have he : self.value = UScalar.mk (ty := .U64) (CrcPartialSpec.physical 64 self.crc.algorithm.refin state) :=
    (UScalar.eq_equiv_bv_eq _ _).mpr hs
  refine ⟨{self with value := mid},?_,rfl,hv⟩
  simp only [CrcBody.crc64.DigestAU64Table.update,he,hm,bind_ok]
end CrcPartial64
