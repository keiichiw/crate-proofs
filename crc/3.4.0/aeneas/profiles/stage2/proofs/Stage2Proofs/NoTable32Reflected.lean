import CrcBody.Funs
import Stage2Proofs.ReflectMathWide
import Stage2Proofs.Reflected32Base
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace CrcReflectedNoTable32

theorem utility_eq (poly value : U32) (reflect : Bool) :
    CrcBody.util.crc32 poly reflect value = crc.util.crc32 poly reflect value := by rfl

@[step] theorem utility_spec (poly value : U32) :
    WP.spec (CrcBody.util.crc32 poly true value)
      (fun out => out.bv = crc.polynomialRun poly.bv true 8 value.bv) := by
  obtain ⟨out, hout, hv⟩ := crc.crc32_polynomial_spec poly value true
  rw [utility_eq, hout]
  exact (WP.spec_ok out).mpr hv

def step (poly state : U32) (byte : U8) : U32 :=
  UScalar.mk (crc.polynomialRun poly.bv true 8
    ((state.bv ^^^ byte.bv.setWidth 32) &&& (255 : BitVec 32)) ^^^
      (state.bv >>> 8))

def run (poly initial : U32) (bytes : List U8) : U32 := bytes.foldl (step poly) initial

theorem body_spec (poly : U32) (bytes : Slice U8) (state : U32) (i : Usize)
    (hi : i.val < bytes.val.length) :
    WP.spec (CrcBody.crc32.update_table_loop7.body bytes (Slice.len bytes) true poly state i)
      (fun out => ∃ j, out = .cont (step poly state bytes.val[i.val], j) ∧
        j.val = i.val + 1) := by
  unfold CrcBody.crc32.update_table_loop7.body
  simp only [UScalar.lt_equiv, Slice.len_val, hi, ↓reduceIte]
  step
  step
  step
  step
  step
  step
  step
  step
  refine ⟨i6, ?_, i6_post⟩
  apply congrArg (fun v : U32 => ControlFlow.cont (v, i6))
  unfold step
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  simp only [crc1_post1, i4_post, to_crc_post1, i3_post1, i2_post, i1_post,
    i5_post1, UScalar.cast]
  rfl

theorem loop_spec (poly : U32) (bytes : Slice U8) (initial : U32) :
    WP.spec (CrcBody.crc32.update_table_loop7 initial bytes (Slice.len bytes) 0#usize true poly)
      (fun out => out = run poly initial bytes.val) := by
  unfold CrcBody.crc32.update_table_loop7
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
    · unfold CrcBody.crc32.update_table_loop7.body
      simp only [UScalar.lt_equiv, Slice.len_val, hlt, ↓reduceIte, WP.spec_ok]
      have heq : i.val = bytes.val.length := by omega
      simpa [run, heq] using hr
  · simp

theorem update_table_total (algorithm : CrcBody.crc_catalog.Algorithm U32)
    (table : Array (Array U32 256#usize) 0#usize) (bytes : Slice U8) (initial : U32)
    (hw : algorithm.width = 32#u8) (hr : algorithm.refin = true) :
    ∃ out, CrcBody.crc32.update_table initial algorithm table bytes = .ok out ∧
      out = run (CrcReflectedPublic32.reverseScalar algorithm.poly) initial bytes.val := by
  apply crc.total_result
  unfold CrcBody.crc32.update_table
  simp only [show (0#usize : Usize) ≠ 16#usize by decide, ↓reduceIte,
    show ¬(0#usize : Usize) > 0#usize by decide, hr, hw, CrcReflectedPublic32.reverse32, bind_ok]
  step
  have hz : poly.val = 0 := by omega
  step
  have heq : poly = CrcReflectedPublic32.reverseScalar algorithm.poly := by
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    simpa only [hz, BitVec.ushiftRight_zero] using poly_post1
  subst poly
  exact loop_spec (CrcReflectedPublic32.reverseScalar algorithm.poly) bytes initial


theorem step_decoded (poly state : U32) (byte : U8) :
    (step (CrcReflectedPublic32.reverseScalar poly) state byte).bv.reverse =
      CrcReflectedWide.byteStep poly.bv state.bv.reverse byte.bv := by
  have hshift : ((state.bv ^^^ byte.bv.setWidth 32) >>> 8) = state.bv >>> 8 := by
    rw [BitVec.ushiftRight_xor_distrib]
    have hz : (byte.bv.setWidth 32 >>> 8) = 0 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have hb : byte.bv.getLsbD (8+i) = false := BitVec.getLsbD_of_ge _ _ (by omega)
      simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, hb]
    rw [hz]
    simp
  have hs : (step (CrcReflectedPublic32.reverseScalar poly) state byte).bv =
      (CrcReflectedWide.byteStep poly.bv state.bv.reverse byte.bv).reverse := by
    rw [CrcReflectedWide.byteStep_injection (by decide)]
    simp only [BitVec.reverse_reverse_eq]
    conv_rhs => rw [CrcReflectedWide.polynomialRun_split8 (by decide)]
    rw [hshift]
    exact BitVec.xor_comm _ _
  exact (congrArg BitVec.reverse hs).trans BitVec.reverse_reverse_eq

theorem run_decoded (poly state : U32) (bytes : List U8) :
    (run (CrcReflectedPublic32.reverseScalar poly) state bytes).bv.reverse =
      CrcReflectedWide.run poly.bv state.bv.reverse (bytes.map UScalar.bv) := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte bytes ih =>
    simp only [run, List.foldl_cons, List.map_cons, CrcReflectedWide.run]
    exact (ih (step (CrcReflectedPublic32.reverseScalar poly) state byte)).trans
      (congrArg (fun x => CrcReflectedWide.run poly.bv x (bytes.map UScalar.bv))
        (step_decoded poly state byte))

abbrev Crc32 := CrcBody.Crc U32 (CrcBody.Table 0#usize) (Array (Array U32 256#usize) 0#usize)
abbrev Digest32 := CrcBody.Digest U32 (CrcBody.Table 0#usize) (Array (Array U32 256#usize) 0#usize)

theorem update_canonical (self : Crc32) (state : U32) (bytes : Slice U8)
    (ha : CrcReflectedPublic32.Domain self.algorithm) :
    ∃ out, CrcBody.crc32.CrcU32Table.update self state bytes = .ok out ∧
      out.bv.reverse = CrcReflectedWide.run self.algorithm.poly.bv state.bv.reverse
        (bytes.val.map UScalar.bv) := by
  obtain ⟨out, hout, hv⟩ := update_table_total self.algorithm self.data bytes state ha.1 ha.2
  exact ⟨out, hout, (congrArg (fun x : U32 => x.bv.reverse) hv).trans (run_decoded _ _ _)⟩

theorem checksum_canonical (self : Crc32) (bytes : Slice U8)
    (ha : CrcReflectedPublic32.Domain self.algorithm) :
    ∃ out, CrcBody.crc32.CrcU32Table.checksum self bytes = .ok out ∧
      out.bv = CrcReflectedPublic32.finish self.algorithm (CrcReflectedWide.run self.algorithm.poly.bv
        self.algorithm.init.bv (bytes.val.map UScalar.bv)) := by
  obtain ⟨mid, hm, hv⟩ := update_canonical self (CrcReflectedPublic32.reverseScalar self.algorithm.init) bytes ha
  obtain ⟨out, hf, hout⟩ := CrcReflectedPublic32.finalize_canonical self.algorithm mid ha
  refine ⟨out, ?_, hout.trans ?_⟩
  · simp only [CrcBody.crc32.CrcU32Table.checksum, CrcReflectedPublic32.init_eq _ _ ha, hm, bind_ok, hf]
  · apply congrArg (CrcReflectedPublic32.finish self.algorithm)
    simpa only [CrcReflectedPublic32.reverseScalar_bv, BitVec.reverse_reverse_eq] using hv

theorem digest_update_canonical (self : Digest32) (bytes : Slice U8)
    (ha : CrcReflectedPublic32.Domain self.crc.algorithm) :
    ∃ out, CrcBody.crc32.DigestAU32Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv.reverse =
        CrcReflectedWide.run self.crc.algorithm.poly.bv self.value.bv.reverse
          (bytes.val.map UScalar.bv) := by
  obtain ⟨mid, hm, hv⟩ := update_canonical self.crc self.value bytes ha
  exact ⟨{self with value := mid}, by simp [CrcBody.crc32.DigestAU32Table.update, hm], rfl, hv⟩
theorem digest_initial (self : Crc32) (initial : U32)
    (ha : CrcReflectedPublic32.Domain self.algorithm) :
    CrcBody.crc32.CrcU32Table.digest_with_initial self initial =
      .ok ⟨self, CrcReflectedPublic32.reverseScalar initial⟩ := by
  simp only [CrcBody.crc32.CrcU32Table.digest_with_initial, CrcReflectedPublic32.init_eq _ _ ha,
    bind_ok, CrcBody.crc32.DigestAU32Table.new]

theorem digest_protocol_canonical (self : Crc32) (initial : U32) (bytes : Slice U8)
    (ha : CrcReflectedPublic32.Domain self.algorithm) :
    ∃ start stop out,
      CrcBody.crc32.CrcU32Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc32.DigestAU32Table.update start bytes = .ok stop ∧
      CrcBody.crc32.DigestAU32Table.finalize stop = .ok out ∧
      out.bv = CrcReflectedPublic32.finish self.algorithm
        (CrcReflectedWide.run self.algorithm.poly.bv initial.bv (bytes.val.map UScalar.bv)) := by
  obtain ⟨stop, hu, hc, hv⟩ := digest_update_canonical
    (⟨self, CrcReflectedPublic32.reverseScalar initial⟩ : Digest32) bytes ha
  have hsa : CrcReflectedPublic32.Domain stop.crc.algorithm := by simpa only [hc] using ha
  obtain ⟨out, hf, hout⟩ := CrcReflectedPublic32.finalize_canonical stop.crc.algorithm stop.value hsa
  refine ⟨⟨self, CrcReflectedPublic32.reverseScalar initial⟩, stop, out,
    digest_initial self initial ha, hu, hf, ?_⟩
  have hvc : stop.value.bv.reverse =
      CrcReflectedWide.run self.algorithm.poly.bv initial.bv (bytes.val.map UScalar.bv) := by
    simpa only [CrcReflectedPublic32.reverseScalar_bv, BitVec.reverse_reverse_eq] using hv
  simpa only [hc] using hout.trans (congrArg (CrcReflectedPublic32.finish stop.crc.algorithm) hvc)
end CrcReflectedNoTable32
