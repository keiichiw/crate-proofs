import CrcBody.Funs
import Stage2Proofs.ByteMathWide
import Stage2Proofs.Public32Base
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace CrcNoTable32

theorem utility_eq (poly value : U32) (reflect : Bool) :
    CrcBody.util.crc32 poly reflect value = crc.util.crc32 poly reflect value := by rfl

@[step] theorem utility_spec (poly value : U32) :
    WP.spec (CrcBody.util.crc32 poly false value)
      (fun out => out.bv = crc.polynomialRun poly.bv false 8 (value.bv <<< 24)) := by
  obtain ⟨out, hout, hv⟩ := crc.crc32_polynomial_spec poly value false
  rw [utility_eq, hout]
  exact (WP.spec_ok out).mpr hv

def step (poly state : U32) (byte : U8) : U32 :=
  UScalar.mk (crc.polynomialRun poly.bv false 8
    ((((state.bv >>> 24) ^^^ byte.bv.setWidth 32) &&& (255 : BitVec 32)) <<< 24) ^^^
      (state.bv <<< 8))

def run (poly initial : U32) (bytes : List U8) : U32 := bytes.foldl (step poly) initial

theorem body_spec (poly : U32) (bytes : Slice U8) (state : U32) (i : Usize)
    (hi : i.val < bytes.val.length) :
    WP.spec (CrcBody.crc32.update_table_loop8.body bytes (Slice.len bytes) false poly state i)
      (fun out => ∃ j, out = .cont (step poly state bytes.val[i.val], j) ∧
        j.val = i.val + 1) := by
  unfold CrcBody.crc32.update_table_loop8.body
  simp only [UScalar.lt_equiv, Slice.len_val, hi, ↓reduceIte]
  step
  step
  step
  step
  step
  step
  step
  step
  step
  refine ⟨i7, ?_, i7_post⟩
  apply congrArg (fun v : U32 => ControlFlow.cont (v, i7))
  unfold step
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  simp only [crc1_post1, i5_post, to_crc_post1, i4_post1, i1_post1, i3_post, i2_post,
    i6_post1, UScalar.cast]
  rfl

theorem loop_spec (poly : U32) (bytes : Slice U8) (initial : U32) :
    WP.spec (CrcBody.crc32.update_table_loop8 initial bytes (Slice.len bytes) 0#usize false poly)
      (fun out => out = run poly initial bytes.val) := by
  unfold CrcBody.crc32.update_table_loop8
  apply loop.spec_decr_nat
    (measure := fun x : U32 × Usize => bytes.val.length - x.2.val)
    (inv := fun x : U32 × Usize => x.2.val ≤ bytes.val.length ∧
      run poly x.1 (bytes.val.drop x.2.val) = run poly initial bytes.val)
  · intro x hx
    rcases x with ⟨state, i⟩
    dsimp only at hx
    obtain ⟨hi, hr⟩ := hx
    by_cases hlt : i.val < bytes.val.length
    · apply WP.spec_mono (body_spec poly bytes state i hlt)
      intro out hout
      obtain ⟨j, rfl, hj⟩ := hout
      simp only
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [List.drop_eq_getElem_cons hlt] at hr
      simpa only [run, List.foldl_cons, hj] using hr
    · unfold CrcBody.crc32.update_table_loop8.body
      simp only [UScalar.lt_equiv, Slice.len_val, hlt, ↓reduceIte, WP.spec_ok]
      have heq : i.val = bytes.val.length := by omega
      simpa [run, heq] using hr
  · simp

theorem update_table_total (algorithm : CrcBody.crc_catalog.Algorithm U32)
    (table : Array (Array U32 256#usize) 0#usize) (bytes : Slice U8) (initial : U32)
    (hw : algorithm.width = 32#u8) (hr : algorithm.refin = false) :
    ∃ out, CrcBody.crc32.update_table initial algorithm table bytes = .ok out ∧
      out = run algorithm.poly initial bytes.val := by
  apply crc.total_result
  unfold CrcBody.crc32.update_table
  simp only [show (0#usize : Usize) ≠ 16#usize by decide, ↓reduceIte,
    show ¬(0#usize : Usize) > 0#usize by decide, hr, hw, Bool.false_eq_true]
  step
  have hz : poly.val = 0 := by omega
  step
  have heq : poly = algorithm.poly := by
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    simpa only [hz, BitVec.shiftLeft_zero] using poly_post1
  subst poly
  exact loop_spec algorithm.poly bytes initial

theorem step_canonical (poly state : U32) (byte : U8) :
    (step poly state byte).bv = CrcCanonicalWide.byteStep poly.bv state.bv byte.bv := by
  have hlo : ((state.bv ^^^ (byte.bv.setWidth 32 <<< 24)) <<< 8) = state.bv <<< 8 := by
    rw [BitVec.shiftLeft_xor_distrib, ← BitVec.shiftLeft_add]
    simp
  have hhi : ((state.bv ^^^ (byte.bv.setWidth 32 <<< 24)) >>> 24) <<< 24 =
      (((state.bv >>> 24 ^^^ byte.bv.setWidth 32) &&& 255) <<< 24) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rw [CrcCanonicalWide.byteStep_injection (by decide), CrcCanonicalWide.encodeByte]
  rw [CrcCanonicalWide.polynomialRun_split8 (by decide)]
  change _ = ((state.bv ^^^ (byte.bv.setWidth 32 <<< 24)) <<< 8) ^^^
    crc.polynomialRun poly.bv false 8 (((state.bv ^^^ (byte.bv.setWidth 32 <<< 24)) >>> 24) <<< 24)
  rw [hlo, hhi]
  exact BitVec.xor_comm _ _

theorem run_bv (poly state : U32) (bytes : List U8) :
    (run poly state bytes).bv =
      CrcCanonicalWide.run poly.bv state.bv (bytes.map UScalar.bv) := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte bytes ih =>
    change (run poly (step poly state byte) bytes).bv =
      CrcCanonicalWide.run poly.bv (CrcCanonicalWide.byteStep poly.bv state.bv byte.bv)
        (bytes.map UScalar.bv)
    rw [ih, step_canonical]

abbrev Crc32 := CrcBody.Crc U32 (CrcBody.Table 0#usize) (Array (Array U32 256#usize) 0#usize)
abbrev Digest32 := CrcBody.Digest U32 (CrcBody.Table 0#usize) (Array (Array U32 256#usize) 0#usize)

theorem update32_canonical (self : Crc32) (state : U32) (bytes : Slice U8)
    (hw : self.algorithm.width = 32#u8) (hr : self.algorithm.refin = false) :
    ∃ out, CrcBody.crc32.CrcU32Table.update self state bytes = .ok out ∧
      out.bv = CrcCanonicalWide.run self.algorithm.poly.bv state.bv
        (bytes.val.map UScalar.bv) := by
  obtain ⟨out, hout, hv⟩ := update_table_total self.algorithm self.data bytes state hw hr
  exact ⟨out, hout, (congrArg UScalar.bv hv).trans (run_bv _ _ _)⟩

/-- NoTable update, arbitrary polynomial and messages, full-width nonreflected input. -/
theorem digest32_update_canonical (self : Digest32) (bytes : Slice U8)
    (hw : self.crc.algorithm.width = 32#u8) (hr : self.crc.algorithm.refin = false) :
    ∃ out, CrcBody.crc32.DigestAU32Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv =
        CrcCanonicalWide.run self.crc.algorithm.poly.bv self.value.bv
          (bytes.val.map UScalar.bv) := by
  obtain ⟨mid, hm, hv⟩ := update32_canonical self.crc self.value bytes hw hr
  exact ⟨{self with value := mid}, by simp [CrcBody.crc32.DigestAU32Table.update, hm], rfl, hv⟩

/-- Full-width NoTable checksum, nonreflected input and either output reflection. -/
theorem checksum32_canonical (self : Crc32) (bytes : Slice U8)
    (ha : CrcPublic32.NonRef32 self.algorithm) :
    ∃ out, CrcBody.crc32.CrcU32Table.checksum self bytes = .ok out ∧
      out.bv = (if self.algorithm.refout then
        (CrcCanonicalWide.run self.algorithm.poly.bv self.algorithm.init.bv
          (bytes.val.map UScalar.bv)).reverse else
        CrcCanonicalWide.run self.algorithm.poly.bv self.algorithm.init.bv
          (bytes.val.map UScalar.bv)) ^^^ self.algorithm.xorout.bv := by
  obtain ⟨mid, hm, hv⟩ := update32_canonical self self.algorithm.init bytes ha.1 ha.2
  obtain ⟨out, hout, ho⟩ := CrcPublic32.finalize_total self.algorithm mid ha
  refine ⟨out, ?_, ?_⟩
  · simp only [CrcBody.crc32.CrcU32Table.checksum, CrcPublic32.init_identity _ _ ha,
      hm, bind_ok, hout]
  · simpa only [hv] using ho

end CrcNoTable32
