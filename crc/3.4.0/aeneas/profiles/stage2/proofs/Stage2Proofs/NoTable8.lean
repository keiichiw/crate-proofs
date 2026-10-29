import CrcBody.Funs
import Stage2Proofs.ByteMath
import Stage2Proofs.Public8
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace CrcNoTable8

theorem utility_eq (poly value : U8) (reflect : Bool) :
    CrcBody.util.crc8 poly reflect value = crc.util.crc8 poly reflect value := by rfl

def step (poly state byte : U8) : U8 :=
  UScalar.mk (CrcCanonical8.byteStep poly.bv state.bv byte.bv)

def run (poly initial : U8) (bytes : List U8) : U8 := bytes.foldl (step poly) initial

theorem utility_step (poly state byte : U8) :
    CrcBody.util.crc8 poly false (state ^^^ byte) = .ok (step poly state byte) := by
  obtain ⟨out, hout, hv⟩ := crc.crc8_polynomial_spec poly (state ^^^ byte) false
  rw [utility_eq, hout]
  congr 1
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  exact hv.trans (CrcCanonical8.byteStep_injection poly.bv state.bv byte.bv).symm

theorem body_spec (poly : U8) (bytes : Slice U8) (state : U8) (i : Usize)
    (hi : i.val < bytes.val.length) :
    WP.spec (CrcBody.crc8.update_table_loop4.body false bytes (Slice.len bytes) poly state i)
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
    WP.spec (CrcBody.crc8.update_table_loop4 initial false bytes (Slice.len bytes) 0#usize poly)
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
    (hw : algorithm.width = 8#u8) (hr : algorithm.refin = false) :
    ∃ out, CrcBody.crc8.update_table initial algorithm table bytes = .ok out ∧
      out = run algorithm.poly initial bytes.val := by
  apply crc.total_result
  unfold CrcBody.crc8.update_table
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

theorem run_bv (poly state : U8) (bytes : List U8) :
    (run poly state bytes).bv =
      CrcCanonical8.run poly.bv state.bv (bytes.map UScalar.bv) := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte bytes ih => exact ih (step poly state byte)

abbrev Crc8 := CrcBody.Crc U8 (CrcBody.Table 0#usize) (Array (Array U8 256#usize) 0#usize)
abbrev Digest8 := CrcBody.Digest U8 (CrcBody.Table 0#usize) (Array (Array U8 256#usize) 0#usize)

theorem update8_canonical (self : Crc8) (state : U8) (bytes : Slice U8)
    (hw : self.algorithm.width = 8#u8) (hr : self.algorithm.refin = false) :
    ∃ out, CrcBody.crc8.CrcU8Table.update self state bytes = .ok out ∧
      out.bv = CrcCanonical8.run self.algorithm.poly.bv state.bv
        (bytes.val.map UScalar.bv) := by
  obtain ⟨out, hout, hv⟩ := update_table_total self.algorithm self.data bytes state hw hr
  exact ⟨out, hout, (congrArg UScalar.bv hv).trans (run_bv _ _ _)⟩

/-- Actual checksum, arbitrary polynomial/init/xorout/messages, NoTable, fullwidth nonreflected. -/
theorem checksum8_canonical (self : Crc8) (bytes : Slice U8)
    (ha : CrcBody.FullWidth8 self.algorithm) :
    ∃ out, CrcBody.crc8.CrcU8Table.checksum self bytes = .ok out ∧
      out.bv = CrcCanonical8.run self.algorithm.poly.bv self.algorithm.init.bv
        (bytes.val.map UScalar.bv) ^^^ self.algorithm.xorout.bv := by
  obtain ⟨mid, hm, hv⟩ := update8_canonical self self.algorithm.init bytes ha.1 ha.2.1
  refine ⟨mid ^^^ self.algorithm.xorout, ?_, ?_⟩
  · simp only [CrcBody.crc8.CrcU8Table.checksum, CrcBody.init8_identity _ _ ha, hm,
      Aeneas.Std.bind_ok, CrcBody.finalize8_xor _ _ ha]
  · exact congrArg (fun x : BitVec 8 => x ^^^ self.algorithm.xorout.bv) hv

/-- Actual mutable digest update preserves its Crc and returns canonical message state. -/
theorem digest8_update_canonical (self : Digest8) (bytes : Slice U8)
    (hw : self.crc.algorithm.width = 8#u8) (hr : self.crc.algorithm.refin = false) :
    ∃ out, CrcBody.crc8.DigestAU8Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv =
        CrcCanonical8.run self.crc.algorithm.poly.bv self.value.bv
          (bytes.val.map UScalar.bv) := by
  obtain ⟨mid, hm, hv⟩ := update8_canonical self.crc self.value bytes hw hr
  exact ⟨{self with value := mid}, by simp [CrcBody.crc8.DigestAU8Table.update, hm], rfl, hv⟩

/-- Streaming two slices equals updating their concatenation, with no cached table invariant. -/
theorem digest8_update_append (self : Digest8) (xs ys whole : Slice U8)
    (hwhole : whole.val = xs.val ++ ys.val)
    (hw : self.crc.algorithm.width = 8#u8) (hr : self.crc.algorithm.refin = false) :
    ∃ mid final, CrcBody.crc8.DigestAU8Table.update self xs = .ok mid ∧
      CrcBody.crc8.DigestAU8Table.update mid ys = .ok final ∧
      CrcBody.crc8.DigestAU8Table.update self whole = .ok final := by
  obtain ⟨v1, hv1, hrun1⟩ := update_table_total self.crc.algorithm self.crc.data xs self.value hw hr
  obtain ⟨v2, hv2, hrun2⟩ := update_table_total self.crc.algorithm self.crc.data ys v1 hw hr
  obtain ⟨v3, hv3, hrun3⟩ := update_table_total self.crc.algorithm self.crc.data whole self.value hw hr
  have heq : v3 = v2 := by
    rw [hrun3, hwhole, run, List.foldl_append]
    change run self.crc.algorithm.poly (run self.crc.algorithm.poly self.value xs.val) ys.val = v2
    rw [← hrun1, ← hrun2]
  refine ⟨{self with value := v1}, {self with value := v2}, ?_, ?_, ?_⟩
  · simp only [CrcBody.crc8.DigestAU8Table.update, CrcBody.crc8.CrcU8Table.update, hv1, bind_ok]
  · simp only [CrcBody.crc8.DigestAU8Table.update, CrcBody.crc8.CrcU8Table.update, hv2, bind_ok]
  · simp only [CrcBody.crc8.DigestAU8Table.update, CrcBody.crc8.CrcU8Table.update, hv3, bind_ok, heq]

end CrcNoTable8
