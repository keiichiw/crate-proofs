import Stage2Proofs.FullWidth16
import Stage2Proofs.WidthEndpoints
import Stage2Proofs.PartialSpec
open Aeneas Aeneas.Std Result
namespace CrcPartial16

def TableCoherent {w : Nat} (refin : Bool) (poly : BitVec w) (table : CrcUpdate16.Table) : Prop :=
  ∀ byte : U8, (CrcPublic16.tableRead table byte).bv = CrcPartialSpec.tableEntry 16 refin poly byte.bv

def surrogate {w : Nat} (self : CrcPublic16.Crc16) (poly : BitVec w) : CrcPublic16.Crc16 :=
  {self with algorithm := {self.algorithm with poly := UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 poly)}}

theorem table_run_nonref {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 16)
    (poly state : BitVec w) (self : CrcPublic16.Crc16) (bytes : List U8)
    (ht : TableCoherent false poly self.data) :
    (CrcUpdate16.run self.data (UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 state)) bytes).bv =
      CrcWidthEncoding.encode 16 (CrcCanonicalWide.run poly state (bytes.map UScalar.bv)) := by
  have hc : CrcPublic16.Coherent16 (surrogate self poly) := by
    intro b
    have hb := ht b
    refine hb.trans ?_
    change CrcWidthEncoding.encode 16 (CrcCanonicalWide.byteStep poly 0 b.bv) = _
    rw [CrcWidthEncoding.encode_byteStep hw hN]
    have hz : CrcWidthEncoding.encode 16 (0 : BitVec w) = 0 := by simp [CrcWidthEncoding.encode]
    rw [hz]
    rfl
  have hf := CrcPublic16.run_canonical (surrogate self poly) hc
    (UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 state)) bytes
  exact hf.trans (CrcWidthEncoding.encode_run hw hN poly state (bytes.map (fun x : U8 => x.bv))).symm

theorem table_run_reflected {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 16)
    (poly state : BitVec w) (self : CrcPublic16.Crc16) (bytes : List U8)
    (ht : TableCoherent true poly self.data) :
    (CrcUpdate16Reflected.run self.data
      (UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 state).reverse) bytes).bv =
      (CrcWidthEncoding.encode 16 (CrcReflectedWide.run poly state (bytes.map UScalar.bv))).reverse := by
  have hc : CrcReflectedTable16.Coherent (surrogate self poly) := by
    intro b
    have hb := ht b
    refine hb.trans ?_
    change (CrcWidthEncoding.encode 16 (CrcReflectedWide.byteStep poly 0 b.bv)).reverse = _
    rw [CrcWidthEndpoints.encode_reflected_byteStep hw hN]
    have hz : CrcWidthEncoding.encode 16 (0 : BitVec w) = 0 := by simp [CrcWidthEncoding.encode]
    rw [hz]
    rfl
  have hf := CrcReflectedTable16.run_canonical (surrogate self poly) hc
    (UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 state).reverse) bytes
  have ha : (UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 state).reverse).bv.reverse =
      CrcWidthEncoding.encode 16 state := BitVec.reverse_reverse_eq
  have hargs := congrArg (fun x : BitVec 16 => (CrcReflectedWide.run
    (CrcWidthEncoding.encode 16 poly) x (bytes.map UScalar.bv)).reverse) ha
  exact hf.trans (hargs.trans (congrArg BitVec.reverse
    (CrcWidthEndpoints.encode_reflected_run hw hN poly state (bytes.map (fun x : U8 => x.bv))).symm))

theorem update_table1_encoded (self : CrcPublic16.Crc16) (bytes : Slice U8)
    (poly state : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 16)
    (ht : TableCoherent self.algorithm.refin poly self.data) :
    ∃ out, CrcBody.crc16.CrcU16Table.update self
      (UScalar.mk (ty := .U16) (CrcPartialSpec.physical 16 self.algorithm.refin state)) bytes = .ok out ∧
      out.bv = CrcPartialSpec.physical 16 self.algorithm.refin
        (CrcPartialSpec.run self.algorithm.refin poly state (bytes.val.map UScalar.bv)) := by
  cases hr : self.algorithm.refin with
  | false =>
    obtain ⟨out, ho, hv⟩ := CrcUpdate16.update_table_total self.algorithm self.data bytes
      (UScalar.mk (ty := .U16) (CrcPartialSpec.physical 16 self.algorithm.refin state)) hr
    simp only [hr] at ho hv
    refine ⟨out, ho, ?_⟩
    have ht' : TableCoherent false poly self.data := by simpa only [hr] using ht
    have he := table_run_nonref hw.1 hw.2 poly state self bytes.val ht'
    exact (congrArg UScalar.bv hv).trans he
  | true =>
    obtain ⟨out, ho, hv⟩ := CrcUpdate16Reflected.update_table_total self.algorithm self.data bytes
      (UScalar.mk (ty := .U16) (CrcPartialSpec.physical 16 self.algorithm.refin state)) hr
    simp only [hr] at ho hv
    refine ⟨out, ho, ?_⟩
    have ht' : TableCoherent true poly self.data := by simpa only [hr] using ht
    have he := table_run_reflected hw.1 hw.2 poly state self bytes.val ht'
    exact (congrArg UScalar.bv hv).trans he
theorem checksum_table1 (self : CrcPublic16.Crc16) (bytes : Slice U8)
    (poly initial xorout : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 16)
    (_hp : self.algorithm.poly.bv = poly.setWidth 16)
    (hi : self.algorithm.init.bv = initial.setWidth 16)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 16)
    (ht : TableCoherent self.algorithm.refin poly self.data) :
    ∃ out, CrcBody.crc16.CrcU16Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout
        poly initial xorout (bytes.val.map UScalar.bv)).setWidth 16 := by
  have hl : self.algorithm.init.bv.setWidth self.algorithm.width.val = initial := by
    rw [hi, BitVec.setWidth_setWidth_of_le initial hw.2]
    simp
  have hinit := CrcWidthEndpoints.init16_eq_encoded self.algorithm self.algorithm.init hw
  rw [hl] at hinit
  obtain ⟨mid, hm, hmid⟩ := update_table1_encoded self bytes poly initial hw ht
  let resultState : BitVec self.algorithm.width.val :=
    CrcPartialSpec.run self.algorithm.refin poly initial (bytes.val.map (fun b : U8 => b.bv))
  have hmid' : mid.bv = CrcWidthEndpoints.storedEncode 16 self.algorithm.refin resultState := hmid
  obtain ⟨out, ho, hv⟩ := CrcWidthEndpoints.finalize16_encoded self.algorithm mid xorout resultState hw hx hmid' 
  refine ⟨out, ?_, hv⟩
  simp only [CrcBody.crc16.CrcU16Table.checksum, hinit, hm, ho, bind_ok]


theorem digest_update_table1 (self : CrcPublic16.Digest16) (bytes : Slice U8)
    (poly state : BitVec self.crc.algorithm.width.val)
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 16)
    (_hp : self.crc.algorithm.poly.bv = poly.setWidth 16)
    (hs : self.value.bv = CrcPartialSpec.physical 16 self.crc.algorithm.refin state)
    (ht : TableCoherent self.crc.algorithm.refin poly self.crc.data) :
    ∃ out, CrcBody.crc16.DigestAU16Table.update self bytes = .ok out ∧ out.crc = self.crc ∧
      out.value.bv = CrcPartialSpec.physical 16 self.crc.algorithm.refin
        (CrcPartialSpec.run self.crc.algorithm.refin poly state (bytes.val.map UScalar.bv)) := by
  obtain ⟨mid, hm, hv⟩ := update_table1_encoded self.crc bytes poly state hw ht
  have he : self.value = UScalar.mk (ty := .U16) (CrcPartialSpec.physical 16 self.crc.algorithm.refin state) := by
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    exact hs
  refine ⟨{self with value := mid}, ?_, rfl, hv⟩
  simp only [CrcBody.crc16.DigestAU16Table.update, he, hm, bind_ok]


theorem protocol_table1 (self : CrcPublic16.Crc16) (initial : U16) (bytes : Slice U8)
    (poly xorout : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 16)
    (_hp : self.algorithm.poly.bv = poly.setWidth 16)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 16)
    (ht : TableCoherent self.algorithm.refin poly self.data) :
    ∃ start final out,
      CrcBody.crc16.CrcU16Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc16.DigestAU16Table.update start bytes = .ok final ∧
      CrcBody.crc16.DigestAU16Table.finalize final = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout poly
        (initial.bv.setWidth self.algorithm.width.val) xorout (bytes.val.map UScalar.bv)).setWidth 16 := by
  let initialState := initial.bv.setWidth self.algorithm.width.val
  let storage := UScalar.mk (ty := .U16) (CrcPartialSpec.physical 16 self.algorithm.refin initialState)
  obtain ⟨mid, hm, hmid⟩ := update_table1_encoded self bytes poly initialState hw ht
  let resultState : BitVec self.algorithm.width.val :=
    CrcPartialSpec.run self.algorithm.refin poly initialState (bytes.val.map (fun b : U8 => b.bv))
  have hmid' : mid.bv = CrcWidthEndpoints.storedEncode 16 self.algorithm.refin resultState := hmid
  obtain ⟨out, ho, hv⟩ := CrcWidthEndpoints.finalize16_encoded self.algorithm mid xorout resultState hw hx hmid'
  refine ⟨⟨self,storage⟩, ⟨self,mid⟩, out, ?_, ?_, ho, hv⟩
  · simp only [CrcBody.crc16.CrcU16Table.digest_with_initial,
      CrcWidthEndpoints.init16_eq_encoded _ _ hw, bind_ok, CrcBody.crc16.DigestAU16Table.new]
    rfl
  · dsimp only [storage]
    simp only [CrcBody.crc16.DigestAU16Table.update, hm, bind_ok]


theorem prepared_poly (a : CrcBody.crc_catalog.Algorithm U16) (poly : BitVec a.width.val)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 16) (hp : a.poly.bv = poly.setWidth 16) :
    CrcBody.crc16.init a a.poly = .ok (UScalar.mk (ty := .U16) (CrcPartialSpec.physical 16 a.refin poly)) := by
  have hl : a.poly.bv.setWidth a.width.val = poly := by
    rw [hp, BitVec.setWidth_setWidth_of_le poly hw.2]
    simp
  simpa only [hl] using CrcWidthEndpoints.init16_eq_encoded a a.poly hw


theorem notable_run_nonref {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 16)
    (poly state : BitVec w) (bytes : List U8) :
    (CrcNoTable16.run (UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 poly))
      (UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 state)) bytes).bv =
      CrcWidthEncoding.encode 16 (CrcCanonicalWide.run poly state (bytes.map UScalar.bv)) := by
  have hf := CrcNoTable16.run_bv (UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 poly))
    (UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 state)) bytes
  exact hf.trans (CrcWidthEncoding.encode_run hw hN poly state (bytes.map (fun x : U8 => x.bv))).symm

theorem notable_run_reflected {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 16)
    (poly state : BitVec w) (bytes : List U8) :
    (CrcReflectedNoTable16.run (UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 poly).reverse)
      (UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 state).reverse) bytes).bv =
      (CrcWidthEncoding.encode 16 (CrcReflectedWide.run poly state (bytes.map UScalar.bv))).reverse := by
  have hf := CrcReflectedNoTable16.run_decoded (UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 poly))
    (UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 state).reverse) bytes
  have harg : (UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 state).reverse).bv.reverse =
      CrcWidthEncoding.encode 16 state := BitVec.reverse_reverse_eq
  have hf' := hf.trans (congrArg (fun x : BitVec 16 => CrcReflectedWide.run
    (CrcWidthEncoding.encode 16 poly) x (bytes.map UScalar.bv)) harg)
  have he := (CrcWidthEndpoints.encode_reflected_run hw hN poly state (bytes.map (fun x : U8 => x.bv))).symm
  exact BitVec.reverse_reverse_eq.symm.trans (congrArg BitVec.reverse (hf'.trans he))

theorem update_notable_encoded (self : CrcNoTable16.Crc16) (bytes : Slice U8)
    (poly state : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 16)
    (hp : self.algorithm.poly.bv = poly.setWidth 16) :
    ∃ out, CrcBody.crc16.CrcU16Table.update self
      (UScalar.mk (ty := .U16) (CrcPartialSpec.physical 16 self.algorithm.refin state)) bytes = .ok out ∧
      out.bv = CrcPartialSpec.physical 16 self.algorithm.refin
        (CrcPartialSpec.run self.algorithm.refin poly state (bytes.val.map UScalar.bv)) := by
  apply crc.total_result
  unfold CrcBody.crc16.CrcU16Table.update CrcBody.crc16.update_table
  simp only [show (0#usize : Usize) ≠ 16#usize by decide, ↓reduceIte,
    show ¬(0#usize : Usize) > 0#usize by decide]
  change WP.spec (do
    let pp ← CrcBody.crc16.init self.algorithm self.algorithm.poly
    if self.algorithm.refin then
      CrcBody.crc16.update_table_loop7
        (UScalar.mk (ty := .U16) (CrcPartialSpec.physical 16 self.algorithm.refin state))
        bytes (Slice.len bytes) 0#usize self.algorithm.refin pp
    else
      CrcBody.crc16.update_table_loop8
        (UScalar.mk (ty := .U16) (CrcPartialSpec.physical 16 self.algorithm.refin state))
        bytes (Slice.len bytes) 0#usize self.algorithm.refin pp) _
  rw [prepared_poly self.algorithm poly hw hp]
  simp only [bind_ok]
  cases hr : self.algorithm.refin with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    change WP.spec (CrcBody.crc16.update_table_loop8
      (UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 state)) bytes (Slice.len bytes) 0#usize false
      (UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 poly)))
      (fun out => out.bv = CrcWidthEncoding.encode 16 (CrcCanonicalWide.run poly state (bytes.val.map UScalar.bv)))
    apply WP.spec_mono (CrcNoTable16.loop_spec _ bytes _)
    intro out ho
    exact (congrArg UScalar.bv ho).trans (notable_run_nonref hw.1 hw.2 poly state bytes.val)
  | true =>
    simp only [↓reduceIte]
    change WP.spec (CrcBody.crc16.update_table_loop7
      (UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 state).reverse) bytes (Slice.len bytes) 0#usize true
      (UScalar.mk (ty := .U16) (CrcWidthEncoding.encode 16 poly).reverse))
      (fun out => out.bv = (CrcWidthEncoding.encode 16 (CrcReflectedWide.run poly state (bytes.val.map UScalar.bv))).reverse)
    apply WP.spec_mono (CrcReflectedNoTable16.loop_spec _ bytes _)
    intro out ho
    exact (congrArg UScalar.bv ho).trans (notable_run_reflected hw.1 hw.2 poly state bytes.val)
theorem checksum_notable (self : CrcNoTable16.Crc16) (bytes : Slice U8)
    (poly initial xorout : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 16)
    (hp : self.algorithm.poly.bv = poly.setWidth 16)
    (hi : self.algorithm.init.bv = initial.setWidth 16)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 16) :
    ∃ out, CrcBody.crc16.CrcU16Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout
        poly initial xorout (bytes.val.map UScalar.bv)).setWidth 16 := by
  have hl : self.algorithm.init.bv.setWidth self.algorithm.width.val = initial := by
    rw [hi, BitVec.setWidth_setWidth_of_le initial hw.2]
    simp
  have hinit := CrcWidthEndpoints.init16_eq_encoded self.algorithm self.algorithm.init hw
  rw [hl] at hinit
  obtain ⟨mid, hm, hmid⟩ := update_notable_encoded self bytes poly initial hw hp
  let resultState : BitVec self.algorithm.width.val :=
    CrcPartialSpec.run self.algorithm.refin poly initial (bytes.val.map (fun b : U8 => b.bv))
  have hmid' : mid.bv = CrcWidthEndpoints.storedEncode 16 self.algorithm.refin resultState := hmid
  obtain ⟨out, ho, hv⟩ := CrcWidthEndpoints.finalize16_encoded self.algorithm mid xorout resultState hw hx hmid' 
  refine ⟨out, ?_, hv⟩
  simp only [CrcBody.crc16.CrcU16Table.checksum, hinit, hm, ho, bind_ok]


theorem digest_update_notable (self : CrcNoTable16.Digest16) (bytes : Slice U8)
    (poly state : BitVec self.crc.algorithm.width.val)
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 16)
    (hp : self.crc.algorithm.poly.bv = poly.setWidth 16)
    (hs : self.value.bv = CrcPartialSpec.physical 16 self.crc.algorithm.refin state) :
    ∃ out, CrcBody.crc16.DigestAU16Table.update self bytes = .ok out ∧ out.crc = self.crc ∧
      out.value.bv = CrcPartialSpec.physical 16 self.crc.algorithm.refin
        (CrcPartialSpec.run self.crc.algorithm.refin poly state (bytes.val.map UScalar.bv)) := by
  obtain ⟨mid, hm, hv⟩ := update_notable_encoded self.crc bytes poly state hw hp
  have he : self.value = UScalar.mk (ty := .U16) (CrcPartialSpec.physical 16 self.crc.algorithm.refin state) := by
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    exact hs
  refine ⟨{self with value := mid}, ?_, rfl, hv⟩
  simp only [CrcBody.crc16.DigestAU16Table.update, he, hm, bind_ok]


theorem protocol_notable (self : CrcNoTable16.Crc16) (initial : U16) (bytes : Slice U8)
    (poly xorout : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 16)
    (hp : self.algorithm.poly.bv = poly.setWidth 16)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 16) :
    ∃ start final out,
      CrcBody.crc16.CrcU16Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc16.DigestAU16Table.update start bytes = .ok final ∧
      CrcBody.crc16.DigestAU16Table.finalize final = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout poly
        (initial.bv.setWidth self.algorithm.width.val) xorout (bytes.val.map UScalar.bv)).setWidth 16 := by
  let initialState := initial.bv.setWidth self.algorithm.width.val
  let storage := UScalar.mk (ty := .U16) (CrcPartialSpec.physical 16 self.algorithm.refin initialState)
  obtain ⟨mid, hm, hmid⟩ := update_notable_encoded self bytes poly initialState hw hp
  let resultState : BitVec self.algorithm.width.val :=
    CrcPartialSpec.run self.algorithm.refin poly initialState (bytes.val.map (fun b : U8 => b.bv))
  have hmid' : mid.bv = CrcWidthEndpoints.storedEncode 16 self.algorithm.refin resultState := hmid
  obtain ⟨out, ho, hv⟩ := CrcWidthEndpoints.finalize16_encoded self.algorithm mid xorout resultState hw hx hmid'
  refine ⟨⟨self,storage⟩, ⟨self,mid⟩, out, ?_, ?_, ho, hv⟩
  · simp only [CrcBody.crc16.CrcU16Table.digest_with_initial,
      CrcWidthEndpoints.init16_eq_encoded _ _ hw, bind_ok, CrcBody.crc16.DigestAU16Table.new]
    rfl
  · dsimp only [storage]
    simp only [CrcBody.crc16.DigestAU16Table.update, hm, bind_ok]
end CrcPartial16
