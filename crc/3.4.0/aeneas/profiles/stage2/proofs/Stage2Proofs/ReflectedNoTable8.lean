import CrcBody.Funs
import Stage2Proofs.ByteMath
import Stage2Proofs.Reflected8
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace CrcReflectedNoTable8

theorem utility_eq (poly value : U8) (reflect : Bool) :
    CrcBody.util.crc8 poly reflect value = crc.util.crc8 poly reflect value := by rfl

def step (poly state byte : U8) : U8 :=
  UScalar.mk (crc.polynomialRun poly.bv true 8 (state.bv ^^^ byte.bv))

def run (poly initial : U8) (bytes : List U8) : U8 := bytes.foldl (step poly) initial

theorem utility_step (poly state byte : U8) :
    CrcBody.util.crc8 poly true (state ^^^ byte) = .ok (step poly state byte) := by
  obtain ⟨out, hout, hv⟩ := crc.crc8_polynomial_spec poly (state ^^^ byte) true
  rw [utility_eq, hout]
  congr 1
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  exact hv

theorem body_spec (poly : U8) (bytes : Slice U8) (state : U8) (i : Usize)
    (hi : i.val < bytes.val.length) :
    WP.spec (CrcBody.crc8.update_table_loop4.body true bytes (Slice.len bytes) poly state i)
      (fun out => ∃ j, out = .cont (step poly state bytes.val[i.val], j) ∧
        j.val = i.val + 1) := by
  unfold CrcBody.crc8.update_table_loop4.body
  simp only [UScalar.lt_equiv, Slice.len_val, hi, ↓reduceIte]
  step
  step
  have heq : i2 = state ^^^ i1 := (UScalar.eq_equiv_bv_eq _ _).mpr i2_post1
  rw [heq]
  subst i1
  rw [utility_step]
  simp only [bind_ok]
  step
  exact ⟨i3, rfl, i3_post⟩

theorem loop_spec (poly : U8) (bytes : Slice U8) (initial : U8) :
    WP.spec (CrcBody.crc8.update_table_loop4 initial true bytes (Slice.len bytes) 0#usize poly)
      (fun out => out = run poly initial bytes.val) := by
  unfold CrcBody.crc8.update_table_loop4
  apply loop.spec_decr_nat
    (measure := fun x : U8 × Usize => bytes.val.length - x.2.val)
    (inv := fun x : U8 × Usize => x.2.val ≤ bytes.val.length ∧
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
    · unfold CrcBody.crc8.update_table_loop4.body
      simp only [UScalar.lt_equiv, Slice.len_val, hlt, ↓reduceIte, WP.spec_ok]
      have heq : i.val = bytes.val.length := by omega
      simpa [run, heq] using hr
  · simp

theorem update_table_total (algorithm : CrcBody.crc_catalog.Algorithm U8)
    (table : Array (Array U8 256#usize) 0#usize) (bytes : Slice U8) (initial : U8)
    (ha : CrcReflectedPublic8.Domain algorithm) :
    ∃ out, CrcBody.crc8.update_table initial algorithm table bytes = .ok out ∧
      out = run (CrcReflectedPublic8.reverseScalar algorithm.poly) initial bytes.val := by
  apply crc.total_result
  unfold CrcBody.crc8.update_table
  obtain ⟨hw, hr⟩ := ha
  simp only [show (0#usize : Usize) ≠ 16#usize by decide, ↓reduceIte,
    show ¬(0#usize : Usize) > 0#usize by decide, hr, hw,
    CrcReflectedPublic8.reverse8, bind_ok]
  step
  have hz : poly.val = 0 := by omega
  step
  have heq : poly = CrcReflectedPublic8.reverseScalar algorithm.poly := by
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    simpa only [hz, BitVec.ushiftRight_zero] using poly_post1
  subst poly
  exact loop_spec (CrcReflectedPublic8.reverseScalar algorithm.poly) bytes initial

theorem step_decoded (poly state byte : U8) :
    (step (CrcReflectedPublic8.reverseScalar poly) state byte).bv.reverse =
      CrcReflected8.byteStep poly.bv state.bv.reverse byte.bv := by
  have h := CrcReflected8.byteStep_injection poly.bv state.bv.reverse byte.bv
  have hs : (step (CrcReflectedPublic8.reverseScalar poly) state byte).bv =
      (CrcReflected8.byteStep poly.bv state.bv.reverse byte.bv).reverse := by
    change crc.polynomialRun poly.bv.reverse true 8 (state.bv ^^^ byte.bv) = _
    simpa only [BitVec.reverse_reverse_eq] using h.symm
  exact (congrArg BitVec.reverse hs).trans BitVec.reverse_reverse_eq

theorem run_decoded (poly state : U8) (bytes : List U8) :
    (run (CrcReflectedPublic8.reverseScalar poly) state bytes).bv.reverse =
      CrcReflected8.run poly.bv state.bv.reverse (bytes.map UScalar.bv) := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte bytes ih =>
    simp only [run, List.foldl_cons, List.map_cons, CrcReflected8.run]
    exact (ih (step (CrcReflectedPublic8.reverseScalar poly) state byte)).trans
      (congrArg (fun x => CrcReflected8.run poly.bv x (bytes.map UScalar.bv))
        (step_decoded poly state byte))

abbrev Crc8 := CrcBody.Crc U8 (CrcBody.Table 0#usize) (Array (Array U8 256#usize) 0#usize)
abbrev Digest8 := CrcBody.Digest U8 (CrcBody.Table 0#usize) (Array (Array U8 256#usize) 0#usize)

theorem update_canonical (self : Crc8) (state : U8) (bytes : Slice U8)
    (ha : CrcReflectedPublic8.Domain self.algorithm) :
    ∃ out, CrcBody.crc8.CrcU8Table.update self state bytes = .ok out ∧
      out.bv.reverse = CrcReflected8.run self.algorithm.poly.bv state.bv.reverse
        (bytes.val.map UScalar.bv) := by
  obtain ⟨out, hout, hv⟩ := update_table_total self.algorithm self.data bytes state ha
  exact ⟨out, hout, (congrArg (fun x : U8 => x.bv.reverse) hv).trans (run_decoded _ _ _)⟩

theorem checksum_canonical (self : Crc8) (bytes : Slice U8)
    (ha : CrcReflectedPublic8.Domain self.algorithm) :
    ∃ out, CrcBody.crc8.CrcU8Table.checksum self bytes = .ok out ∧
      out.bv = CrcReflectedPublic8.finish self.algorithm (CrcReflected8.run self.algorithm.poly.bv
        self.algorithm.init.bv (bytes.val.map UScalar.bv)) := by
  obtain ⟨mid, hm, hv⟩ := update_canonical self (CrcReflectedPublic8.reverseScalar self.algorithm.init) bytes ha
  obtain ⟨out, hf, hout⟩ := CrcReflectedPublic8.finalize_canonical self.algorithm mid ha
  refine ⟨out, ?_, hout.trans ?_⟩
  · simp only [CrcBody.crc8.CrcU8Table.checksum, CrcReflectedPublic8.init_eq _ _ ha, hm, bind_ok, hf]
  · apply congrArg (CrcReflectedPublic8.finish self.algorithm)
    simpa only [CrcReflectedPublic8.reverseScalar_bv, BitVec.reverse_reverse_eq] using hv

theorem digest_update_canonical (self : Digest8) (bytes : Slice U8)
    (ha : CrcReflectedPublic8.Domain self.crc.algorithm) :
    ∃ out, CrcBody.crc8.DigestAU8Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv.reverse =
        CrcReflected8.run self.crc.algorithm.poly.bv self.value.bv.reverse
          (bytes.val.map UScalar.bv) := by
  obtain ⟨mid, hm, hv⟩ := update_canonical self.crc self.value bytes ha
  exact ⟨{self with value := mid}, by simp [CrcBody.crc8.DigestAU8Table.update, hm], rfl, hv⟩
theorem digest_initial (self : Crc8) (initial : U8)
    (ha : CrcReflectedPublic8.Domain self.algorithm) :
    CrcBody.crc8.CrcU8Table.digest_with_initial self initial =
      .ok ⟨self, CrcReflectedPublic8.reverseScalar initial⟩ := by
  simp only [CrcBody.crc8.CrcU8Table.digest_with_initial, CrcReflectedPublic8.init_eq _ _ ha,
    bind_ok, CrcBody.crc8.DigestAU8Table.new]

theorem digest_protocol_canonical (self : Crc8) (initial : U8) (bytes : Slice U8)
    (ha : CrcReflectedPublic8.Domain self.algorithm) :
    ∃ start stop out,
      CrcBody.crc8.CrcU8Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc8.DigestAU8Table.update start bytes = .ok stop ∧
      CrcBody.crc8.DigestAU8Table.finalize stop = .ok out ∧
      out.bv = CrcReflectedPublic8.finish self.algorithm
        (CrcReflected8.run self.algorithm.poly.bv initial.bv (bytes.val.map UScalar.bv)) := by
  obtain ⟨stop, hu, hc, hv⟩ := digest_update_canonical
    (⟨self, CrcReflectedPublic8.reverseScalar initial⟩ : Digest8) bytes ha
  have hsa : CrcReflectedPublic8.Domain stop.crc.algorithm := by simpa only [hc] using ha
  obtain ⟨out, hf, hout⟩ := CrcReflectedPublic8.finalize_canonical stop.crc.algorithm stop.value hsa
  refine ⟨⟨self, CrcReflectedPublic8.reverseScalar initial⟩, stop, out,
    digest_initial self initial ha, hu, hf, ?_⟩
  have hvc : stop.value.bv.reverse =
      CrcReflected8.run self.algorithm.poly.bv initial.bv (bytes.val.map UScalar.bv) := by
    simpa only [CrcReflectedPublic8.reverseScalar_bv, BitVec.reverse_reverse_eq] using hv
  simpa only [hc] using hout.trans (congrArg (CrcReflectedPublic8.finish stop.crc.algorithm) hvc)
end CrcReflectedNoTable8
