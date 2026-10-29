import Stage2Proofs.FullWidth8
import Stage2Proofs.WidthEndpoints
import Stage2Proofs.PartialSpec
open Aeneas Aeneas.Std Result
namespace CrcPartial8

def TableCoherent {w : Nat} (refin : Bool) (poly : BitVec w) (table : CrcUpdate8.Table) : Prop :=
  ∀ byte : U8, (CrcUpdate8.tableRead table byte).bv =
    CrcPartialSpec.tableEntry 8 refin poly byte.bv

theorem table_run_nonref {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 8)
    (poly state : BitVec w) (table : CrcUpdate8.Table) (bytes : List U8)
    (ht : TableCoherent false poly table) :
    (CrcUpdate8.run table (UScalar.mk (ty := .U8) (CrcWidthEncoding.encode 8 state)) bytes).bv =
      CrcWidthEncoding.encode 8 (CrcCanonicalWide.run poly state (bytes.map UScalar.bv)) := by
  have htable : CrcCanonical8.TableValid (CrcWidthEncoding.encode 8 poly) (CrcBody.tableFunction table) := by
    intro b
    have hb := ht (UScalar.mk (ty := .U8) b)
    change (CrcUpdate8.tableRead table (UScalar.mk (ty := .U8) b)).bv = _
    refine hb.trans ?_
    change CrcWidthEncoding.encode 8 (CrcCanonicalWide.byteStep poly 0 b) = _
    rw [CrcWidthEncoding.encode_byteStep hw hN]
    have hz : CrcWidthEncoding.encode 8 (0 : BitVec w) = 0 := by simp [CrcWidthEncoding.encode]
    rw [hz]
    rfl
  have hf := CrcBody.fold8_bv table (UScalar.mk (ty := .U8) (CrcWidthEncoding.encode 8 state)) bytes
  have hc := CrcCanonical8.lookupRun_correct (CrcWidthEncoding.encode 8 poly) (CrcBody.tableFunction table)
    htable (CrcWidthEncoding.encode 8 state) (bytes.map UScalar.bv)
  have he := (CrcWidthEncoding.encode_run hw hN poly state (bytes.map (fun x : U8 => x.bv))).symm
  have hrun : CrcCanonical8.run (CrcWidthEncoding.encode 8 poly) (CrcWidthEncoding.encode 8 state)
      (bytes.map UScalar.bv) = CrcCanonicalWide.run (CrcWidthEncoding.encode 8 poly)
        (CrcWidthEncoding.encode 8 state) (bytes.map UScalar.bv) := by rfl
  exact hf.trans (hc.trans (hrun.trans he))

theorem table_run_reflected {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 8)
    (poly state : BitVec w) (table : CrcUpdate8.Table) (bytes : List U8)
    (ht : TableCoherent true poly table) :
    (CrcUpdate8.run table
      (UScalar.mk (ty := .U8) (CrcWidthEncoding.encode 8 state).reverse) bytes).bv =
      (CrcWidthEncoding.encode 8 (CrcReflectedWide.run poly state (bytes.map UScalar.bv))).reverse := by
  have htable : CrcReflected8.TableValid (CrcWidthEncoding.encode 8 poly) (CrcBody.tableFunction table) := by
    intro b
    have hb := ht (UScalar.mk (ty := .U8) b)
    change (CrcUpdate8.tableRead table (UScalar.mk (ty := .U8) b)).bv = _
    refine hb.trans ?_
    change (CrcWidthEncoding.encode 8 (CrcReflectedWide.byteStep poly 0 b)).reverse = _
    rw [CrcWidthEndpoints.encode_reflected_byteStep hw hN]
    have hz : CrcWidthEncoding.encode 8 (0 : BitVec w) = 0 := by simp [CrcWidthEncoding.encode]
    rw [hz, CrcReflectedWide.byteStep_injection (by decide)]
    apply congrArg (crc.polynomialRun (CrcWidthEncoding.encode 8 poly).reverse true 8)
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [BitVec.getLsbD_reverse]
  have hf := CrcBody.fold8_bv table
    (UScalar.mk (ty := .U8) (CrcWidthEncoding.encode 8 state).reverse) bytes
  have hc := CrcReflected8.lookupRun_correct (CrcWidthEncoding.encode 8 poly) (CrcBody.tableFunction table)
    htable (CrcWidthEncoding.encode 8 state) (bytes.map UScalar.bv)
  have hr : CrcReflected8.run (CrcWidthEncoding.encode 8 poly) (CrcWidthEncoding.encode 8 state)
      (bytes.map UScalar.bv) = CrcReflectedWide.run (CrcWidthEncoding.encode 8 poly)
        (CrcWidthEncoding.encode 8 state) (bytes.map UScalar.bv) := by rfl
  exact hf.trans (hc.trans (congrArg BitVec.reverse
    (hr.trans (CrcWidthEndpoints.encode_reflected_run hw hN poly state (bytes.map UScalar.bv)).symm)))

theorem table_run {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 8) (refin : Bool)
    (poly state : BitVec w) (table : CrcUpdate8.Table) (bytes : List U8)
    (ht : TableCoherent refin poly table) :
    (CrcUpdate8.run table (UScalar.mk (ty := .U8) (CrcPartialSpec.physical 8 refin state)) bytes).bv =
      CrcPartialSpec.physical 8 refin (CrcPartialSpec.run refin poly state (bytes.map UScalar.bv)) := by
  cases refin with
  | false => exact table_run_nonref hw hN poly state table bytes ht
  | true => exact table_run_reflected hw hN poly state table bytes ht

theorem update_table1_encoded (self : CrcBody.Crc8) (bytes : Slice U8)
    (poly state : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 8)
    (ht : TableCoherent self.algorithm.refin poly self.data) :
    ∃ out, CrcBody.crc8.CrcU8Table.update self
      (UScalar.mk (ty := .U8) (CrcPartialSpec.physical 8 self.algorithm.refin state)) bytes = .ok out ∧
      out.bv = CrcPartialSpec.physical 8 self.algorithm.refin
        (CrcPartialSpec.run self.algorithm.refin poly state (bytes.val.map UScalar.bv)) := by
  obtain ⟨out, hout, hv⟩ := CrcUpdate8.update_table_total self.algorithm self.data bytes
    (UScalar.mk (ty := .U8) (CrcPartialSpec.physical 8 self.algorithm.refin state))
  exact ⟨out, hout, (congrArg UScalar.bv hv).trans (table_run hw.1 hw.2 _ poly state self.data bytes.val ht)⟩

theorem checksum_table1 (self : CrcBody.Crc8) (bytes : Slice U8)
    (poly initial xorout : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 8)
    (_hp : self.algorithm.poly.bv = poly.setWidth 8)
    (hi : self.algorithm.init.bv = initial.setWidth 8)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 8)
    (ht : TableCoherent self.algorithm.refin poly self.data) :
    ∃ out, CrcBody.crc8.CrcU8Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout
        poly initial xorout (bytes.val.map UScalar.bv)).setWidth 8 := by
  have hl : self.algorithm.init.bv.setWidth self.algorithm.width.val = initial := by
    rw [hi, BitVec.setWidth_setWidth_of_le initial hw.2]
    simp
  have hinit := CrcWidthEndpoints.init8_eq_encoded self.algorithm self.algorithm.init hw
  rw [hl] at hinit
  obtain ⟨mid, hm, hmid⟩ := update_table1_encoded self bytes poly initial hw ht
  let resultState : BitVec self.algorithm.width.val :=
    CrcPartialSpec.run self.algorithm.refin poly initial (bytes.val.map (fun b : U8 => b.bv))
  have hmid' : mid.bv = CrcWidthEndpoints.storedEncode 8 self.algorithm.refin resultState := hmid
  obtain ⟨out, ho, hv⟩ := CrcWidthEndpoints.finalize8_encoded self.algorithm mid xorout resultState hw hx hmid' 
  refine ⟨out, ?_, hv⟩
  simp only [CrcBody.crc8.CrcU8Table.checksum, hinit, hm, ho, bind_ok]

theorem digest_update_table1 (self : CrcBody.Digest8) (bytes : Slice U8)
    (poly state : BitVec self.crc.algorithm.width.val)
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 8)
    (_hp : self.crc.algorithm.poly.bv = poly.setWidth 8)
    (hs : self.value.bv = CrcPartialSpec.physical 8 self.crc.algorithm.refin state)
    (ht : TableCoherent self.crc.algorithm.refin poly self.crc.data) :
    ∃ out, CrcBody.crc8.DigestAU8Table.update self bytes = .ok out ∧ out.crc = self.crc ∧
      out.value.bv = CrcPartialSpec.physical 8 self.crc.algorithm.refin
        (CrcPartialSpec.run self.crc.algorithm.refin poly state (bytes.val.map UScalar.bv)) := by
  obtain ⟨mid, hm, hv⟩ := update_table1_encoded self.crc bytes poly state hw ht
  have he : self.value = UScalar.mk (ty := .U8) (CrcPartialSpec.physical 8 self.crc.algorithm.refin state) := by
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    exact hs
  refine ⟨{self with value := mid}, ?_, rfl, hv⟩
  simp only [CrcBody.crc8.DigestAU8Table.update, he, hm, bind_ok]

theorem protocol_table1 (self : CrcBody.Crc8) (initial : U8) (bytes : Slice U8)
    (poly xorout : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 8)
    (_hp : self.algorithm.poly.bv = poly.setWidth 8)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 8)
    (ht : TableCoherent self.algorithm.refin poly self.data) :
    ∃ start final out,
      CrcBody.crc8.CrcU8Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc8.DigestAU8Table.update start bytes = .ok final ∧
      CrcBody.crc8.DigestAU8Table.finalize final = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout poly
        (initial.bv.setWidth self.algorithm.width.val) xorout (bytes.val.map UScalar.bv)).setWidth 8 := by
  let initialState := initial.bv.setWidth self.algorithm.width.val
  let storage := UScalar.mk (ty := .U8) (CrcPartialSpec.physical 8 self.algorithm.refin initialState)
  obtain ⟨mid, hm, hmid⟩ := update_table1_encoded self bytes poly initialState hw ht
  let resultState : BitVec self.algorithm.width.val :=
    CrcPartialSpec.run self.algorithm.refin poly initialState (bytes.val.map (fun b : U8 => b.bv))
  have hmid' : mid.bv = CrcWidthEndpoints.storedEncode 8 self.algorithm.refin resultState := hmid
  obtain ⟨out, ho, hv⟩ := CrcWidthEndpoints.finalize8_encoded self.algorithm mid xorout resultState hw hx hmid'
  refine ⟨⟨self,storage⟩, ⟨self,mid⟩, out, ?_, ?_, ho, hv⟩
  · simp only [CrcBody.crc8.CrcU8Table.digest_with_initial,
      CrcWidthEndpoints.init8_eq_encoded _ _ hw, bind_ok, CrcBody.crc8.DigestAU8Table.new]
    rfl
  · dsimp only [storage]
    simp only [CrcBody.crc8.DigestAU8Table.update, hm, bind_ok]

theorem notable_run_nonref {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 8)
    (poly state : BitVec w) (bytes : List U8) :
    (CrcNoTable8.run (UScalar.mk (ty := .U8) (CrcWidthEncoding.encode 8 poly))
      (UScalar.mk (ty := .U8) (CrcWidthEncoding.encode 8 state)) bytes).bv =
      CrcWidthEncoding.encode 8 (CrcCanonicalWide.run poly state (bytes.map UScalar.bv)) := by
  have hf := CrcNoTable8.run_bv (UScalar.mk (ty := .U8) (CrcWidthEncoding.encode 8 poly))
    (UScalar.mk (ty := .U8) (CrcWidthEncoding.encode 8 state)) bytes
  have he := (CrcWidthEncoding.encode_run hw hN poly state (bytes.map (fun x : U8 => x.bv))).symm
  have hr : CrcCanonical8.run (CrcWidthEncoding.encode 8 poly) (CrcWidthEncoding.encode 8 state)
      (bytes.map UScalar.bv) = CrcCanonicalWide.run (CrcWidthEncoding.encode 8 poly)
        (CrcWidthEncoding.encode 8 state) (bytes.map UScalar.bv) := by rfl
  exact hf.trans (hr.trans he)

theorem notable_run_reflected {w : Nat} (hw : 1 ≤ w) (hN : w ≤ 8)
    (poly state : BitVec w) (bytes : List U8) :
    (CrcReflectedNoTable8.run (UScalar.mk (ty := .U8) (CrcWidthEncoding.encode 8 poly).reverse)
      (UScalar.mk (ty := .U8) (CrcWidthEncoding.encode 8 state).reverse) bytes).bv =
      (CrcWidthEncoding.encode 8 (CrcReflectedWide.run poly state (bytes.map UScalar.bv))).reverse := by
  have hf := CrcReflectedNoTable8.run_decoded (UScalar.mk (ty := .U8) (CrcWidthEncoding.encode 8 poly))
    (UScalar.mk (ty := .U8) (CrcWidthEncoding.encode 8 state).reverse) bytes
  have harg : (UScalar.mk (ty := .U8) (CrcWidthEncoding.encode 8 state).reverse).bv.reverse =
      CrcWidthEncoding.encode 8 state := BitVec.reverse_reverse_eq
  have hf' : (CrcReflectedNoTable8.run (UScalar.mk (ty := .U8) (CrcWidthEncoding.encode 8 poly).reverse)
      (UScalar.mk (ty := .U8) (CrcWidthEncoding.encode 8 state).reverse) bytes).bv.reverse =
      CrcReflected8.run (CrcWidthEncoding.encode 8 poly) (CrcWidthEncoding.encode 8 state)
        (bytes.map UScalar.bv) := by
    exact hf.trans (congrArg (fun x : BitVec 8 => CrcReflected8.run (CrcWidthEncoding.encode 8 poly)
      x (bytes.map UScalar.bv)) harg)
  have he := (CrcWidthEndpoints.encode_reflected_run hw hN poly state (bytes.map (fun x : U8 => x.bv))).symm
  have hr : CrcReflected8.run (CrcWidthEncoding.encode 8 poly) (CrcWidthEncoding.encode 8 state)
      (bytes.map UScalar.bv) = CrcReflectedWide.run (CrcWidthEncoding.encode 8 poly)
        (CrcWidthEncoding.encode 8 state) (bytes.map UScalar.bv) := by rfl
  have hh := congrArg BitVec.reverse (hf'.trans (hr.trans he))
  exact BitVec.reverse_reverse_eq.symm.trans hh

theorem prepared_poly (a : CrcBody.crc_catalog.Algorithm U8) (poly : BitVec a.width.val)
    (hw : 1 ≤ a.width.val ∧ a.width.val ≤ 8) (hp : a.poly.bv = poly.setWidth 8) :
    CrcBody.crc8.init a a.poly = .ok (UScalar.mk (ty := .U8) (CrcPartialSpec.physical 8 a.refin poly)) := by
  have hl : a.poly.bv.setWidth a.width.val = poly := by
    rw [hp, BitVec.setWidth_setWidth_of_le poly hw.2]
    simp
  simpa only [hl] using CrcWidthEndpoints.init8_eq_encoded a a.poly hw

theorem update_notable_encoded (self : CrcNoTable8.Crc8) (bytes : Slice U8)
    (poly state : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 8)
    (hp : self.algorithm.poly.bv = poly.setWidth 8) :
    ∃ out, CrcBody.crc8.CrcU8Table.update self
      (UScalar.mk (ty := .U8) (CrcPartialSpec.physical 8 self.algorithm.refin state)) bytes = .ok out ∧
      out.bv = CrcPartialSpec.physical 8 self.algorithm.refin
        (CrcPartialSpec.run self.algorithm.refin poly state (bytes.val.map UScalar.bv)) := by
  apply crc.total_result
  unfold CrcBody.crc8.CrcU8Table.update CrcBody.crc8.update_table
  simp only [show (0#usize : Usize) ≠ 16#usize by decide, ↓reduceIte,
    show ¬(0#usize : Usize) > 0#usize by decide]
  change WP.spec (do
    let pp ← CrcBody.crc8.init self.algorithm self.algorithm.poly
    CrcBody.crc8.update_table_loop4
      (UScalar.mk (ty := .U8) (CrcPartialSpec.physical 8 self.algorithm.refin state))
      self.algorithm.refin bytes (Slice.len bytes) 0#usize pp) _
  rw [prepared_poly self.algorithm poly hw hp]
  simp only [bind_ok]
  cases hr : self.algorithm.refin with
  | false =>
    change WP.spec (CrcBody.crc8.update_table_loop4
      (UScalar.mk (ty := .U8) (CrcWidthEncoding.encode 8 state)) false bytes (Slice.len bytes) 0#usize
      (UScalar.mk (ty := .U8) (CrcWidthEncoding.encode 8 poly)))
      (fun out => out.bv = CrcWidthEncoding.encode 8 (CrcCanonicalWide.run poly state (bytes.val.map UScalar.bv)))
    apply WP.spec_mono (CrcNoTable8.loop_spec _ bytes _)
    intro out ho
    exact (congrArg UScalar.bv ho).trans (notable_run_nonref hw.1 hw.2 poly state bytes.val)
  | true =>
    change WP.spec (CrcBody.crc8.update_table_loop4
      (UScalar.mk (ty := .U8) (CrcWidthEncoding.encode 8 state).reverse) true bytes (Slice.len bytes) 0#usize
      (UScalar.mk (ty := .U8) (CrcWidthEncoding.encode 8 poly).reverse))
      (fun out => out.bv = (CrcWidthEncoding.encode 8 (CrcReflectedWide.run poly state (bytes.val.map UScalar.bv))).reverse)
    apply WP.spec_mono (CrcReflectedNoTable8.loop_spec _ bytes _)
    intro out ho
    exact (congrArg UScalar.bv ho).trans (notable_run_reflected hw.1 hw.2 poly state bytes.val)
theorem checksum_notable (self : CrcNoTable8.Crc8) (bytes : Slice U8)
    (poly initial xorout : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 8)
    (hp : self.algorithm.poly.bv = poly.setWidth 8)
    (hi : self.algorithm.init.bv = initial.setWidth 8)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 8) :
    ∃ out, CrcBody.crc8.CrcU8Table.checksum self bytes = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout
        poly initial xorout (bytes.val.map UScalar.bv)).setWidth 8 := by
  have hl : self.algorithm.init.bv.setWidth self.algorithm.width.val = initial := by
    rw [hi, BitVec.setWidth_setWidth_of_le initial hw.2]
    simp
  have hinit := CrcWidthEndpoints.init8_eq_encoded self.algorithm self.algorithm.init hw
  rw [hl] at hinit
  obtain ⟨mid, hm, hmid⟩ := update_notable_encoded self bytes poly initial hw hp
  let resultState : BitVec self.algorithm.width.val :=
    CrcPartialSpec.run self.algorithm.refin poly initial (bytes.val.map (fun b : U8 => b.bv))
  have hmid' : mid.bv = CrcWidthEndpoints.storedEncode 8 self.algorithm.refin resultState := hmid
  obtain ⟨out, ho, hv⟩ := CrcWidthEndpoints.finalize8_encoded self.algorithm mid xorout resultState hw hx hmid' 
  refine ⟨out, ?_, hv⟩
  simp only [CrcBody.crc8.CrcU8Table.checksum, hinit, hm, ho, bind_ok]

theorem digest_update_notable (self : CrcNoTable8.Digest8) (bytes : Slice U8)
    (poly state : BitVec self.crc.algorithm.width.val)
    (hw : 1 ≤ self.crc.algorithm.width.val ∧ self.crc.algorithm.width.val ≤ 8)
    (hp : self.crc.algorithm.poly.bv = poly.setWidth 8)
    (hs : self.value.bv = CrcPartialSpec.physical 8 self.crc.algorithm.refin state) :
    ∃ out, CrcBody.crc8.DigestAU8Table.update self bytes = .ok out ∧ out.crc = self.crc ∧
      out.value.bv = CrcPartialSpec.physical 8 self.crc.algorithm.refin
        (CrcPartialSpec.run self.crc.algorithm.refin poly state (bytes.val.map UScalar.bv)) := by
  obtain ⟨mid, hm, hv⟩ := update_notable_encoded self.crc bytes poly state hw hp
  have he : self.value = UScalar.mk (ty := .U8) (CrcPartialSpec.physical 8 self.crc.algorithm.refin state) := by
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    exact hs
  refine ⟨{self with value := mid}, ?_, rfl, hv⟩
  simp only [CrcBody.crc8.DigestAU8Table.update, he, hm, bind_ok]

theorem protocol_notable (self : CrcNoTable8.Crc8) (initial : U8) (bytes : Slice U8)
    (poly xorout : BitVec self.algorithm.width.val)
    (hw : 1 ≤ self.algorithm.width.val ∧ self.algorithm.width.val ≤ 8)
    (hp : self.algorithm.poly.bv = poly.setWidth 8)
    (hx : self.algorithm.xorout.bv = xorout.setWidth 8) :
    ∃ start final out,
      CrcBody.crc8.CrcU8Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc8.DigestAU8Table.update start bytes = .ok final ∧
      CrcBody.crc8.DigestAU8Table.finalize final = .ok out ∧
      out.bv = (CrcPartialSpec.checksum self.algorithm.refin self.algorithm.refout poly
        (initial.bv.setWidth self.algorithm.width.val) xorout (bytes.val.map UScalar.bv)).setWidth 8 := by
  let initialState := initial.bv.setWidth self.algorithm.width.val
  let storage := UScalar.mk (ty := .U8) (CrcPartialSpec.physical 8 self.algorithm.refin initialState)
  obtain ⟨mid, hm, hmid⟩ := update_notable_encoded self bytes poly initialState hw hp
  let resultState : BitVec self.algorithm.width.val :=
    CrcPartialSpec.run self.algorithm.refin poly initialState (bytes.val.map (fun b : U8 => b.bv))
  have hmid' : mid.bv = CrcWidthEndpoints.storedEncode 8 self.algorithm.refin resultState := hmid
  obtain ⟨out, ho, hv⟩ := CrcWidthEndpoints.finalize8_encoded self.algorithm mid xorout resultState hw hx hmid'
  refine ⟨⟨self,storage⟩, ⟨self,mid⟩, out, ?_, ?_, ho, hv⟩
  · simp only [CrcBody.crc8.CrcU8Table.digest_with_initial,
      CrcWidthEndpoints.init8_eq_encoded _ _ hw, bind_ok, CrcBody.crc8.DigestAU8Table.new]
    rfl
  · dsimp only [storage]
    simp only [CrcBody.crc8.DigestAU8Table.update, hm, bind_ok]
end CrcPartial8
