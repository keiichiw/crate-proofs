import Crc
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace crc

def step8 (poly value : U8) (reflect : Bool) : U8 :=
  UScalar.mk (ty := .U8) (if reflect then
    (value.bv >>> 1) ^^^ ((value.bv &&& (1 : BitVec 8)) * poly.bv)
  else
    (value.bv <<< 1) ^^^ (((value.bv >>> 7) &&& (1 : BitVec 8)) * poly.bv))

theorem body8_ref_spec (poly value : U8) (i : I32)
    (hi : 0 ≤ i.val ∧ i.val < 8) :
    WP.spec (util.crc8_loop0.body poly value i)
    (fun out => ∃ j, out = .cont (step8 poly value true, j) ∧ j.val = i.val + 1) := by
  unfold util.crc8_loop0.body
  simp only [IScalar.lt_equiv, IScalar.ofInt_val_eq]
  simp only [hi.2, ↓reduceIte]
  step
  step
  step
  · have hb : i2.val ≤ 1 := by
      simpa [i2_post, UScalar.val_and] using (Nat.and_le_right : value.val &&& 1 ≤ 1)
    have hm := Nat.mul_le_mul_right poly.val hb
    simpa only [one_mul] using (le_trans hm (by scalar_tac : 1 * poly.val ≤ U8.max))
  step
  step
  refine ⟨i4, ?_, i4_post⟩
  apply congrArg (fun v : U8 => ControlFlow.cont (v, i4))
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  have hmul : i3.bv = i2.bv * poly.bv := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, UScalar.bv_toNat]
    rw [i3_post]
    apply (Nat.mod_eq_of_lt _).symm
    have := i3.hmax
    scalar_tac
  change value1.bv = (value.bv >>> 1) ^^^ ((value.bv &&& (1 : BitVec 8)) * poly.bv)
  change @Eq (BitVec 8) _ _ at value1_post1
  exact value1_post1.trans (congrArg₂ (fun a b : BitVec 8 => a ^^^ b) i1_post1
    (hmul.trans (congrArg (fun a : BitVec 8 => a * poly.bv) i2_post1)))

theorem body8_msb_spec (poly value : U8) (i : I32)
    (hi : 0 ≤ i.val ∧ i.val < 8) :
    WP.spec (util.crc8_loop1.body poly value i)
    (fun out => ∃ j, out = .cont (step8 poly value false, j) ∧ j.val = i.val + 1) := by
  unfold util.crc8_loop1.body
  simp only [IScalar.lt_equiv, IScalar.ofInt_val_eq]
  simp only [hi.2, ↓reduceIte]
  step
  step
  step
  step
  · have hb : i3.val ≤ 1 := by
      simpa [i3_post, UScalar.val_and] using (Nat.and_le_right : i2.val &&& 1 ≤ 1)
    have hm := Nat.mul_le_mul_right poly.val hb
    simpa only [one_mul] using (le_trans hm (by scalar_tac : 1 * poly.val ≤ U8.max))
  step
  step
  refine ⟨i5, ?_, i5_post⟩
  apply congrArg (fun v : U8 => ControlFlow.cont (v, i5))
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  have hmul : i4.bv = i3.bv * poly.bv := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, UScalar.bv_toNat]
    rw [i4_post]
    apply (Nat.mod_eq_of_lt _).symm
    have := i4.hmax
    scalar_tac
  change value1.bv = (value.bv <<< 1) ^^^ (((value.bv >>> 7) &&& (1 : BitVec 8)) * poly.bv)
  change @Eq (BitVec 8) _ _ at value1_post1
  exact value1_post1.trans (congrArg₂ (fun a b : BitVec 8 => a ^^^ b) i1_post1
    (hmul.trans (congrArg (fun a : BitVec 8 => a * poly.bv)
      (i3_post1.trans (congrArg (fun a : BitVec 8 => a &&& (1 : BitVec 8)) i2_post1)))))

def run8 (poly : U8) (reflect : Bool) : Nat → U8 → U8
  | 0, value => value
  | n+1, value => run8 poly reflect n (step8 poly value reflect)

theorem loop8_ref_spec (poly value : U8) :
    WP.spec (util.crc8_loop0 poly value 0#i32)
      (fun out => out = run8 poly true 8 value) := by
  unfold util.crc8_loop0
  apply loop.spec_decr_nat
    (measure := fun x : U8 × I32 => 8 - x.2.val.toNat)
    (inv := fun x : U8 × I32 => 0 ≤ x.2.val ∧ x.2.val ≤ 8 ∧
      run8 poly true (8 - x.2.val.toNat) x.1 = run8 poly true 8 value)
  · intro x hx
    rcases x with ⟨v, i⟩
    dsimp only at hx
    obtain ⟨hi0, hi8, hr⟩ := hx
    by_cases hlt : i.val < 8
    · apply WP.spec_mono (body8_ref_spec poly v i ⟨hi0, hlt⟩)
      intro out hout
      obtain ⟨j, rfl, hj⟩ := hout
      simp only
      have hrem : 8 - i.val.toNat = (8-j.val.toNat)+1 := by omega
      refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
      rw [hrem, run8] at hr
      exact hr
    · unfold util.crc8_loop0.body
      simp only [IScalar.lt_equiv, IScalar.ofInt_val_eq, hlt, ↓reduceIte,
        WP.spec_ok]
      have heq : i.val.toNat = 8 := by omega
      simpa only [heq, Nat.sub_self, run8] using hr
  · simp [IScalar.ofInt_val_eq]

theorem loop8_msb_spec (poly value : U8) :
    WP.spec (util.crc8_loop1 poly value 0#i32)
      (fun out => out = run8 poly false 8 value) := by
  unfold util.crc8_loop1
  apply loop.spec_decr_nat
    (measure := fun x : U8 × I32 => 8 - x.2.val.toNat)
    (inv := fun x : U8 × I32 => 0 ≤ x.2.val ∧ x.2.val ≤ 8 ∧
      run8 poly false (8 - x.2.val.toNat) x.1 = run8 poly false 8 value)
  · intro x hx
    rcases x with ⟨v, i⟩
    dsimp only at hx
    obtain ⟨hi0, hi8, hr⟩ := hx
    by_cases hlt : i.val < 8
    · apply WP.spec_mono (body8_msb_spec poly v i ⟨hi0, hlt⟩)
      intro out hout
      obtain ⟨j, rfl, hj⟩ := hout
      simp only
      have hrem : 8 - i.val.toNat = (8-j.val.toNat)+1 := by omega
      refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
      rw [hrem, run8] at hr
      exact hr
    · unfold util.crc8_loop1.body
      simp only [IScalar.lt_equiv, IScalar.ofInt_val_eq, hlt, ↓reduceIte,
        WP.spec_ok]
      have heq : i.val.toNat = 8 := by omega
      simpa only [heq, Nat.sub_self, run8] using hr
  · simp [IScalar.ofInt_val_eq]

theorem total_result {α : Type _} {m : Result α} {p : α → Prop}
    (h : WP.spec m p) : ∃ value, m = Result.ok value ∧ p value := by
  cases m using Result.cases with
  | ret value => exact ⟨value, rfl, WP.spec_ok value |>.mp h⟩
  | vis effect k => exact False.elim ((WP.spec_vis effect k).mp h)
  | div => exact False.elim (WP.spec_div.mp h)

theorem crc8_total_spec (poly value : U8) (reflect : Bool) :
    ∃ out, util.crc8 poly reflect value = .ok out ∧
      out = run8 poly reflect 8 value := by
  have h : WP.spec (util.crc8 poly reflect value)
      (fun out => out = run8 poly reflect 8 value) := by
    cases reflect
    · exact loop8_msb_spec poly value
    · exact loop8_ref_spec poly value
  exact total_result h

end crc
