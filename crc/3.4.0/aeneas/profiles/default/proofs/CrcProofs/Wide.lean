import CrcProofs.Util
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace crc

/-- One polynomial register step, chosen by the outgoing bit. -/
def polynomialStep {n : Nat} (poly value : BitVec n) (reflect : Bool) : BitVec n :=
  if reflect then (value >>> 1) ^^^ (if value.getLsbD 0 then poly else 0)
  else (value <<< 1) ^^^ (if value.getLsbD (n-1) then poly else 0)

def polynomialRun {n : Nat} (poly : BitVec n) (reflect : Bool) : Nat → BitVec n → BitVec n
  | 0, value => value
  | k+1, value => polynomialRun poly reflect k (polynomialStep poly value reflect)

def step16 (poly value : U16) (reflect : Bool) : U16 :=
  UScalar.mk (ty := .U16) (if reflect then
    (value.bv >>> 1) ^^^ ((value.bv &&& (1 : BitVec 16)) * poly.bv)
  else
    (value.bv <<< 1) ^^^ (((value.bv >>> 15) &&& (1 : BitVec 16)) * poly.bv))

theorem body16_ref_spec (poly value : U16) (i : I32)
    (hi : 0 ≤ i.val ∧ i.val < 8) :
    WP.spec (util.crc16_loop0.body poly value i)
    (fun out => ∃ j, out = .cont (step16 poly value true, j) ∧ j.val = i.val + 1) := by
  unfold util.crc16_loop0.body
  simp only [IScalar.lt_equiv, IScalar.ofInt_val_eq]
  simp only [hi.2, ↓reduceIte]
  step
  step
  step
  · have hb : i2.val ≤ 1 := by
      simpa [i2_post, UScalar.val_and] using (Nat.and_le_right : value.val &&& 1 ≤ 1)
    have hm := Nat.mul_le_mul_right poly.val hb
    simpa only [one_mul] using (le_trans hm (by scalar_tac : 1 * poly.val ≤ U16.max))
  step
  step
  refine ⟨i4, ?_, i4_post⟩
  apply congrArg (fun v : U16 => ControlFlow.cont (v, i4))
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  have hmul : i3.bv = i2.bv * poly.bv := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, UScalar.bv_toNat]
    rw [i3_post]
    apply (Nat.mod_eq_of_lt _).symm
    have := i3.hmax
    scalar_tac
  change value1.bv = (value.bv >>> 1) ^^^ ((value.bv &&& (1 : BitVec 16)) * poly.bv)
  change @Eq (BitVec 16) _ _ at value1_post1
  exact value1_post1.trans (congrArg₂ (fun a b : BitVec 16 => a ^^^ b) i1_post1
    (hmul.trans (congrArg (fun a : BitVec 16 => a * poly.bv) i2_post1)))

theorem body16_msb_spec (poly value : U16) (i : I32)
    (hi : 0 ≤ i.val ∧ i.val < 8) :
    WP.spec (util.crc16_loop1.body poly value i)
    (fun out => ∃ j, out = .cont (step16 poly value false, j) ∧ j.val = i.val + 1) := by
  unfold util.crc16_loop1.body
  simp only [IScalar.lt_equiv, IScalar.ofInt_val_eq]
  simp only [hi.2, ↓reduceIte]
  step
  step
  step
  step
  · have hb : i3.val ≤ 1 := by
      simpa [i3_post, UScalar.val_and] using (Nat.and_le_right : i2.val &&& 1 ≤ 1)
    have hm := Nat.mul_le_mul_right poly.val hb
    simpa only [one_mul] using (le_trans hm (by scalar_tac : 1 * poly.val ≤ U16.max))
  step
  step
  refine ⟨i5, ?_, i5_post⟩
  apply congrArg (fun v : U16 => ControlFlow.cont (v, i5))
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  have hmul : i4.bv = i3.bv * poly.bv := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, UScalar.bv_toNat]
    rw [i4_post]
    apply (Nat.mod_eq_of_lt _).symm
    have := i4.hmax
    scalar_tac
  change value1.bv = (value.bv <<< 1) ^^^ (((value.bv >>> 15) &&& (1 : BitVec 16)) * poly.bv)
  change @Eq (BitVec 16) _ _ at value1_post1
  exact value1_post1.trans (congrArg₂ (fun a b : BitVec 16 => a ^^^ b) i1_post1
    (hmul.trans (congrArg (fun a : BitVec 16 => a * poly.bv)
      (i3_post1.trans (congrArg (fun a : BitVec 16 => a &&& (1 : BitVec 16)) i2_post1)))))

def run16 (poly : U16) (reflect : Bool) : Nat → U16 → U16
  | 0, value => value
  | n+1, value => run16 poly reflect n (step16 poly value reflect)

theorem loop16_ref_spec (poly value : U16) :
    WP.spec (util.crc16_loop0 poly value 0#i32)
      (fun out => out = run16 poly true 8 value) := by
  unfold util.crc16_loop0
  apply loop.spec_decr_nat
    (measure := fun x : U16 × I32 => 8 - x.2.val.toNat)
    (inv := fun x : U16 × I32 => 0 ≤ x.2.val ∧ x.2.val ≤ 8 ∧
      run16 poly true (8 - x.2.val.toNat) x.1 = run16 poly true 8 value)
  · intro x hx
    rcases x with ⟨v, i⟩
    dsimp only at hx
    obtain ⟨hi0, hi8, hr⟩ := hx
    by_cases hlt : i.val < 8
    · apply WP.spec_mono (body16_ref_spec poly v i ⟨hi0, hlt⟩)
      intro out hout
      obtain ⟨j, rfl, hj⟩ := hout
      simp only
      have hrem : 8 - i.val.toNat = (8-j.val.toNat)+1 := by omega
      refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
      rw [hrem, run16] at hr
      exact hr
    · unfold util.crc16_loop0.body
      simp only [IScalar.lt_equiv, IScalar.ofInt_val_eq, hlt, ↓reduceIte,
        WP.spec_ok]
      have heq : i.val.toNat = 8 := by omega
      simpa only [heq, Nat.sub_self, run16] using hr
  · simp [IScalar.ofInt_val_eq]

theorem loop16_msb_spec (poly value : U16) :
    WP.spec (util.crc16_loop1 poly value 0#i32)
      (fun out => out = run16 poly false 8 value) := by
  unfold util.crc16_loop1
  apply loop.spec_decr_nat
    (measure := fun x : U16 × I32 => 8 - x.2.val.toNat)
    (inv := fun x : U16 × I32 => 0 ≤ x.2.val ∧ x.2.val ≤ 8 ∧
      run16 poly false (8 - x.2.val.toNat) x.1 = run16 poly false 8 value)
  · intro x hx
    rcases x with ⟨v, i⟩
    dsimp only at hx
    obtain ⟨hi0, hi8, hr⟩ := hx
    by_cases hlt : i.val < 8
    · apply WP.spec_mono (body16_msb_spec poly v i ⟨hi0, hlt⟩)
      intro out hout
      obtain ⟨j, rfl, hj⟩ := hout
      simp only
      have hrem : 8 - i.val.toNat = (8-j.val.toNat)+1 := by omega
      refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
      rw [hrem, run16] at hr
      exact hr
    · unfold util.crc16_loop1.body
      simp only [IScalar.lt_equiv, IScalar.ofInt_val_eq, hlt, ↓reduceIte,
        WP.spec_ok]
      have heq : i.val.toNat = 8 := by omega
      simpa only [heq, Nat.sub_self, run16] using hr
  · simp [IScalar.ofInt_val_eq]


def kernel16 (poly : U16) (reflect : Bool) (value : U16) : U16 :=
  run16 poly reflect 8 (if reflect then value else UScalar.mk (ty := .U16) (value.bv <<< 8))

theorem crc16_spec (poly value : U16) (reflect : Bool) :
    WP.spec (util.crc16 poly reflect value) (fun out => out = kernel16 poly reflect value) := by
  unfold util.crc16
  cases reflect with
  | true => exact loop16_ref_spec poly value
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    step
    have heq : value1 = UScalar.mk (ty := .U16) (value.bv <<< 8) := by
      apply (UScalar.eq_equiv_bv_eq _ _).mpr
      exact value1_post1
    subst heq
    exact loop16_msb_spec poly _
def step32 (poly value : U32) (reflect : Bool) : U32 :=
  UScalar.mk (ty := .U32) (if reflect then
    (value.bv >>> 1) ^^^ ((value.bv &&& (1 : BitVec 32)) * poly.bv)
  else
    (value.bv <<< 1) ^^^ (((value.bv >>> 31) &&& (1 : BitVec 32)) * poly.bv))

theorem body32_ref_spec (poly value : U32) (i : I32)
    (hi : 0 ≤ i.val ∧ i.val < 8) :
    WP.spec (util.crc32_loop0.body poly value i)
    (fun out => ∃ j, out = .cont (step32 poly value true, j) ∧ j.val = i.val + 1) := by
  unfold util.crc32_loop0.body
  simp only [IScalar.lt_equiv, IScalar.ofInt_val_eq]
  simp only [hi.2, ↓reduceIte]
  step
  step
  step
  · have hb : i2.val ≤ 1 := by
      simpa [i2_post, UScalar.val_and] using (Nat.and_le_right : value.val &&& 1 ≤ 1)
    have hm := Nat.mul_le_mul_right poly.val hb
    simpa only [one_mul] using (le_trans hm (by scalar_tac : 1 * poly.val ≤ U32.max))
  step
  step
  refine ⟨i4, ?_, i4_post⟩
  apply congrArg (fun v : U32 => ControlFlow.cont (v, i4))
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  have hmul : i3.bv = i2.bv * poly.bv := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, UScalar.bv_toNat]
    rw [i3_post]
    apply (Nat.mod_eq_of_lt _).symm
    have := i3.hmax
    scalar_tac
  change value1.bv = (value.bv >>> 1) ^^^ ((value.bv &&& (1 : BitVec 32)) * poly.bv)
  change @Eq (BitVec 32) _ _ at value1_post1
  exact value1_post1.trans (congrArg₂ (fun a b : BitVec 32 => a ^^^ b) i1_post1
    (hmul.trans (congrArg (fun a : BitVec 32 => a * poly.bv) i2_post1)))

theorem body32_msb_spec (poly value : U32) (i : I32)
    (hi : 0 ≤ i.val ∧ i.val < 8) :
    WP.spec (util.crc32_loop1.body poly value i)
    (fun out => ∃ j, out = .cont (step32 poly value false, j) ∧ j.val = i.val + 1) := by
  unfold util.crc32_loop1.body
  simp only [IScalar.lt_equiv, IScalar.ofInt_val_eq]
  simp only [hi.2, ↓reduceIte]
  step
  step
  step
  step
  · have hb : i3.val ≤ 1 := by
      simpa [i3_post, UScalar.val_and] using (Nat.and_le_right : i2.val &&& 1 ≤ 1)
    have hm := Nat.mul_le_mul_right poly.val hb
    simpa only [one_mul] using (le_trans hm (by scalar_tac : 1 * poly.val ≤ U32.max))
  step
  step
  refine ⟨i5, ?_, i5_post⟩
  apply congrArg (fun v : U32 => ControlFlow.cont (v, i5))
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  have hmul : i4.bv = i3.bv * poly.bv := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, UScalar.bv_toNat]
    rw [i4_post]
    apply (Nat.mod_eq_of_lt _).symm
    have := i4.hmax
    scalar_tac
  change value1.bv = (value.bv <<< 1) ^^^ (((value.bv >>> 31) &&& (1 : BitVec 32)) * poly.bv)
  change @Eq (BitVec 32) _ _ at value1_post1
  exact value1_post1.trans (congrArg₂ (fun a b : BitVec 32 => a ^^^ b) i1_post1
    (hmul.trans (congrArg (fun a : BitVec 32 => a * poly.bv)
      (i3_post1.trans (congrArg (fun a : BitVec 32 => a &&& (1 : BitVec 32)) i2_post1)))))

def run32 (poly : U32) (reflect : Bool) : Nat → U32 → U32
  | 0, value => value
  | n+1, value => run32 poly reflect n (step32 poly value reflect)

theorem loop32_ref_spec (poly value : U32) :
    WP.spec (util.crc32_loop0 poly value 0#i32)
      (fun out => out = run32 poly true 8 value) := by
  unfold util.crc32_loop0
  apply loop.spec_decr_nat
    (measure := fun x : U32 × I32 => 8 - x.2.val.toNat)
    (inv := fun x : U32 × I32 => 0 ≤ x.2.val ∧ x.2.val ≤ 8 ∧
      run32 poly true (8 - x.2.val.toNat) x.1 = run32 poly true 8 value)
  · intro x hx
    rcases x with ⟨v, i⟩
    dsimp only at hx
    obtain ⟨hi0, hi8, hr⟩ := hx
    by_cases hlt : i.val < 8
    · apply WP.spec_mono (body32_ref_spec poly v i ⟨hi0, hlt⟩)
      intro out hout
      obtain ⟨j, rfl, hj⟩ := hout
      simp only
      have hrem : 8 - i.val.toNat = (8-j.val.toNat)+1 := by omega
      refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
      rw [hrem, run32] at hr
      exact hr
    · unfold util.crc32_loop0.body
      simp only [IScalar.lt_equiv, IScalar.ofInt_val_eq, hlt, ↓reduceIte,
        WP.spec_ok]
      have heq : i.val.toNat = 8 := by omega
      simpa only [heq, Nat.sub_self, run32] using hr
  · simp [IScalar.ofInt_val_eq]

theorem loop32_msb_spec (poly value : U32) :
    WP.spec (util.crc32_loop1 poly value 0#i32)
      (fun out => out = run32 poly false 8 value) := by
  unfold util.crc32_loop1
  apply loop.spec_decr_nat
    (measure := fun x : U32 × I32 => 8 - x.2.val.toNat)
    (inv := fun x : U32 × I32 => 0 ≤ x.2.val ∧ x.2.val ≤ 8 ∧
      run32 poly false (8 - x.2.val.toNat) x.1 = run32 poly false 8 value)
  · intro x hx
    rcases x with ⟨v, i⟩
    dsimp only at hx
    obtain ⟨hi0, hi8, hr⟩ := hx
    by_cases hlt : i.val < 8
    · apply WP.spec_mono (body32_msb_spec poly v i ⟨hi0, hlt⟩)
      intro out hout
      obtain ⟨j, rfl, hj⟩ := hout
      simp only
      have hrem : 8 - i.val.toNat = (8-j.val.toNat)+1 := by omega
      refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
      rw [hrem, run32] at hr
      exact hr
    · unfold util.crc32_loop1.body
      simp only [IScalar.lt_equiv, IScalar.ofInt_val_eq, hlt, ↓reduceIte,
        WP.spec_ok]
      have heq : i.val.toNat = 8 := by omega
      simpa only [heq, Nat.sub_self, run32] using hr
  · simp [IScalar.ofInt_val_eq]


def kernel32 (poly : U32) (reflect : Bool) (value : U32) : U32 :=
  run32 poly reflect 8 (if reflect then value else UScalar.mk (ty := .U32) (value.bv <<< 24))

theorem crc32_spec (poly value : U32) (reflect : Bool) :
    WP.spec (util.crc32 poly reflect value) (fun out => out = kernel32 poly reflect value) := by
  unfold util.crc32
  cases reflect with
  | true => exact loop32_ref_spec poly value
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    step
    have heq : value1 = UScalar.mk (ty := .U32) (value.bv <<< 24) := by
      apply (UScalar.eq_equiv_bv_eq _ _).mpr
      exact value1_post1
    subst heq
    exact loop32_msb_spec poly _

def step64 (poly value : U64) (reflect : Bool) : U64 :=
  UScalar.mk (ty := .U64) (if reflect then
    (value.bv >>> 1) ^^^ ((value.bv &&& (1 : BitVec 64)) * poly.bv)
  else
    (value.bv <<< 1) ^^^ (((value.bv >>> 63) &&& (1 : BitVec 64)) * poly.bv))

theorem body64_ref_spec (poly value : U64) (i : I32)
    (hi : 0 ≤ i.val ∧ i.val < 8) :
    WP.spec (util.crc64_loop0.body poly value i)
    (fun out => ∃ j, out = .cont (step64 poly value true, j) ∧ j.val = i.val + 1) := by
  unfold util.crc64_loop0.body
  simp only [IScalar.lt_equiv, IScalar.ofInt_val_eq]
  simp only [hi.2, ↓reduceIte]
  step
  step
  step
  · have hb : i2.val ≤ 1 := by
      simpa [i2_post, UScalar.val_and] using (Nat.and_le_right : value.val &&& 1 ≤ 1)
    have hm := Nat.mul_le_mul_right poly.val hb
    simpa only [one_mul] using (le_trans hm (by scalar_tac : 1 * poly.val ≤ U64.max))
  step
  step
  refine ⟨i4, ?_, i4_post⟩
  apply congrArg (fun v : U64 => ControlFlow.cont (v, i4))
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  have hmul : i3.bv = i2.bv * poly.bv := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, UScalar.bv_toNat]
    rw [i3_post]
    apply (Nat.mod_eq_of_lt _).symm
    have := i3.hmax
    scalar_tac
  change value1.bv = (value.bv >>> 1) ^^^ ((value.bv &&& (1 : BitVec 64)) * poly.bv)
  change @Eq (BitVec 64) _ _ at value1_post1
  exact value1_post1.trans (congrArg₂ (fun a b : BitVec 64 => a ^^^ b) i1_post1
    (hmul.trans (congrArg (fun a : BitVec 64 => a * poly.bv) i2_post1)))

theorem body64_msb_spec (poly value : U64) (i : I32)
    (hi : 0 ≤ i.val ∧ i.val < 8) :
    WP.spec (util.crc64_loop1.body poly value i)
    (fun out => ∃ j, out = .cont (step64 poly value false, j) ∧ j.val = i.val + 1) := by
  unfold util.crc64_loop1.body
  simp only [IScalar.lt_equiv, IScalar.ofInt_val_eq]
  simp only [hi.2, ↓reduceIte]
  step
  step
  step
  step
  · have hb : i3.val ≤ 1 := by
      simpa [i3_post, UScalar.val_and] using (Nat.and_le_right : i2.val &&& 1 ≤ 1)
    have hm := Nat.mul_le_mul_right poly.val hb
    simpa only [one_mul] using (le_trans hm (by scalar_tac : 1 * poly.val ≤ U64.max))
  step
  step
  refine ⟨i5, ?_, i5_post⟩
  apply congrArg (fun v : U64 => ControlFlow.cont (v, i5))
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  have hmul : i4.bv = i3.bv * poly.bv := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, UScalar.bv_toNat]
    rw [i4_post]
    apply (Nat.mod_eq_of_lt _).symm
    have := i4.hmax
    scalar_tac
  change value1.bv = (value.bv <<< 1) ^^^ (((value.bv >>> 63) &&& (1 : BitVec 64)) * poly.bv)
  change @Eq (BitVec 64) _ _ at value1_post1
  exact value1_post1.trans (congrArg₂ (fun a b : BitVec 64 => a ^^^ b) i1_post1
    (hmul.trans (congrArg (fun a : BitVec 64 => a * poly.bv)
      (i3_post1.trans (congrArg (fun a : BitVec 64 => a &&& (1 : BitVec 64)) i2_post1)))))

def run64 (poly : U64) (reflect : Bool) : Nat → U64 → U64
  | 0, value => value
  | n+1, value => run64 poly reflect n (step64 poly value reflect)

theorem loop64_ref_spec (poly value : U64) :
    WP.spec (util.crc64_loop0 poly value 0#i32)
      (fun out => out = run64 poly true 8 value) := by
  unfold util.crc64_loop0
  apply loop.spec_decr_nat
    (measure := fun x : U64 × I32 => 8 - x.2.val.toNat)
    (inv := fun x : U64 × I32 => 0 ≤ x.2.val ∧ x.2.val ≤ 8 ∧
      run64 poly true (8 - x.2.val.toNat) x.1 = run64 poly true 8 value)
  · intro x hx
    rcases x with ⟨v, i⟩
    dsimp only at hx
    obtain ⟨hi0, hi8, hr⟩ := hx
    by_cases hlt : i.val < 8
    · apply WP.spec_mono (body64_ref_spec poly v i ⟨hi0, hlt⟩)
      intro out hout
      obtain ⟨j, rfl, hj⟩ := hout
      simp only
      have hrem : 8 - i.val.toNat = (8-j.val.toNat)+1 := by omega
      refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
      rw [hrem, run64] at hr
      exact hr
    · unfold util.crc64_loop0.body
      simp only [IScalar.lt_equiv, IScalar.ofInt_val_eq, hlt, ↓reduceIte,
        WP.spec_ok]
      have heq : i.val.toNat = 8 := by omega
      simpa only [heq, Nat.sub_self, run64] using hr
  · simp [IScalar.ofInt_val_eq]

theorem loop64_msb_spec (poly value : U64) :
    WP.spec (util.crc64_loop1 poly value 0#i32)
      (fun out => out = run64 poly false 8 value) := by
  unfold util.crc64_loop1
  apply loop.spec_decr_nat
    (measure := fun x : U64 × I32 => 8 - x.2.val.toNat)
    (inv := fun x : U64 × I32 => 0 ≤ x.2.val ∧ x.2.val ≤ 8 ∧
      run64 poly false (8 - x.2.val.toNat) x.1 = run64 poly false 8 value)
  · intro x hx
    rcases x with ⟨v, i⟩
    dsimp only at hx
    obtain ⟨hi0, hi8, hr⟩ := hx
    by_cases hlt : i.val < 8
    · apply WP.spec_mono (body64_msb_spec poly v i ⟨hi0, hlt⟩)
      intro out hout
      obtain ⟨j, rfl, hj⟩ := hout
      simp only
      have hrem : 8 - i.val.toNat = (8-j.val.toNat)+1 := by omega
      refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
      rw [hrem, run64] at hr
      exact hr
    · unfold util.crc64_loop1.body
      simp only [IScalar.lt_equiv, IScalar.ofInt_val_eq, hlt, ↓reduceIte,
        WP.spec_ok]
      have heq : i.val.toNat = 8 := by omega
      simpa only [heq, Nat.sub_self, run64] using hr
  · simp [IScalar.ofInt_val_eq]


def kernel64 (poly : U64) (reflect : Bool) (value : U64) : U64 :=
  run64 poly reflect 8 (if reflect then value else UScalar.mk (ty := .U64) (value.bv <<< 56))

theorem crc64_spec (poly value : U64) (reflect : Bool) :
    WP.spec (util.crc64 poly reflect value) (fun out => out = kernel64 poly reflect value) := by
  unfold util.crc64
  cases reflect with
  | true => exact loop64_ref_spec poly value
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    step
    have heq : value1 = UScalar.mk (ty := .U64) (value.bv <<< 56) := by
      apply (UScalar.eq_equiv_bv_eq _ _).mpr
      exact value1_post1
    subst heq
    exact loop64_msb_spec poly _

def step128 (poly value : U128) (reflect : Bool) : U128 :=
  UScalar.mk (ty := .U128) (if reflect then
    (value.bv >>> 1) ^^^ ((value.bv &&& (1 : BitVec 128)) * poly.bv)
  else
    (value.bv <<< 1) ^^^ (((value.bv >>> 127) &&& (1 : BitVec 128)) * poly.bv))

theorem body128_ref_spec (poly value : U128) (i : I32)
    (hi : 0 ≤ i.val ∧ i.val < 8) :
    WP.spec (util.crc128_loop0.body poly value i)
    (fun out => ∃ j, out = .cont (step128 poly value true, j) ∧ j.val = i.val + 1) := by
  unfold util.crc128_loop0.body
  simp only [IScalar.lt_equiv, IScalar.ofInt_val_eq]
  simp only [hi.2, ↓reduceIte]
  step
  step
  step
  · have hb : i2.val ≤ 1 := by
      simpa [i2_post, UScalar.val_and] using (Nat.and_le_right : value.val &&& 1 ≤ 1)
    have hm := Nat.mul_le_mul_right poly.val hb
    simpa only [one_mul] using (le_trans hm (by scalar_tac : 1 * poly.val ≤ U128.max))
  step
  step
  refine ⟨i4, ?_, i4_post⟩
  apply congrArg (fun v : U128 => ControlFlow.cont (v, i4))
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  have hmul : i3.bv = i2.bv * poly.bv := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, UScalar.bv_toNat]
    rw [i3_post]
    apply (Nat.mod_eq_of_lt _).symm
    have := i3.hmax
    scalar_tac
  change value1.bv = (value.bv >>> 1) ^^^ ((value.bv &&& (1 : BitVec 128)) * poly.bv)
  change @Eq (BitVec 128) _ _ at value1_post1
  exact value1_post1.trans (congrArg₂ (fun a b : BitVec 128 => a ^^^ b) i1_post1
    (hmul.trans (congrArg (fun a : BitVec 128 => a * poly.bv) i2_post1)))

theorem body128_msb_spec (poly value : U128) (i : I32)
    (hi : 0 ≤ i.val ∧ i.val < 8) :
    WP.spec (util.crc128_loop1.body poly value i)
    (fun out => ∃ j, out = .cont (step128 poly value false, j) ∧ j.val = i.val + 1) := by
  unfold util.crc128_loop1.body
  simp only [IScalar.lt_equiv, IScalar.ofInt_val_eq]
  simp only [hi.2, ↓reduceIte]
  step
  step
  step
  step
  · have hb : i3.val ≤ 1 := by
      simpa [i3_post, UScalar.val_and] using (Nat.and_le_right : i2.val &&& 1 ≤ 1)
    have hm := Nat.mul_le_mul_right poly.val hb
    simpa only [one_mul] using (le_trans hm (by scalar_tac : 1 * poly.val ≤ U128.max))
  step
  step
  refine ⟨i5, ?_, i5_post⟩
  apply congrArg (fun v : U128 => ControlFlow.cont (v, i5))
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  have hmul : i4.bv = i3.bv * poly.bv := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, UScalar.bv_toNat]
    rw [i4_post]
    apply (Nat.mod_eq_of_lt _).symm
    have := i4.hmax
    scalar_tac
  change value1.bv = (value.bv <<< 1) ^^^ (((value.bv >>> 127) &&& (1 : BitVec 128)) * poly.bv)
  change @Eq (BitVec 128) _ _ at value1_post1
  exact value1_post1.trans (congrArg₂ (fun a b : BitVec 128 => a ^^^ b) i1_post1
    (hmul.trans (congrArg (fun a : BitVec 128 => a * poly.bv)
      (i3_post1.trans (congrArg (fun a : BitVec 128 => a &&& (1 : BitVec 128)) i2_post1)))))

def run128 (poly : U128) (reflect : Bool) : Nat → U128 → U128
  | 0, value => value
  | n+1, value => run128 poly reflect n (step128 poly value reflect)

theorem loop128_ref_spec (poly value : U128) :
    WP.spec (util.crc128_loop0 poly value 0#i32)
      (fun out => out = run128 poly true 8 value) := by
  unfold util.crc128_loop0
  apply loop.spec_decr_nat
    (measure := fun x : U128 × I32 => 8 - x.2.val.toNat)
    (inv := fun x : U128 × I32 => 0 ≤ x.2.val ∧ x.2.val ≤ 8 ∧
      run128 poly true (8 - x.2.val.toNat) x.1 = run128 poly true 8 value)
  · intro x hx
    rcases x with ⟨v, i⟩
    dsimp only at hx
    obtain ⟨hi0, hi8, hr⟩ := hx
    by_cases hlt : i.val < 8
    · apply WP.spec_mono (body128_ref_spec poly v i ⟨hi0, hlt⟩)
      intro out hout
      obtain ⟨j, rfl, hj⟩ := hout
      simp only
      have hrem : 8 - i.val.toNat = (8-j.val.toNat)+1 := by omega
      refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
      rw [hrem, run128] at hr
      exact hr
    · unfold util.crc128_loop0.body
      simp only [IScalar.lt_equiv, IScalar.ofInt_val_eq, hlt, ↓reduceIte,
        WP.spec_ok]
      have heq : i.val.toNat = 8 := by omega
      simpa only [heq, Nat.sub_self, run128] using hr
  · simp [IScalar.ofInt_val_eq]

theorem loop128_msb_spec (poly value : U128) :
    WP.spec (util.crc128_loop1 poly value 0#i32)
      (fun out => out = run128 poly false 8 value) := by
  unfold util.crc128_loop1
  apply loop.spec_decr_nat
    (measure := fun x : U128 × I32 => 8 - x.2.val.toNat)
    (inv := fun x : U128 × I32 => 0 ≤ x.2.val ∧ x.2.val ≤ 8 ∧
      run128 poly false (8 - x.2.val.toNat) x.1 = run128 poly false 8 value)
  · intro x hx
    rcases x with ⟨v, i⟩
    dsimp only at hx
    obtain ⟨hi0, hi8, hr⟩ := hx
    by_cases hlt : i.val < 8
    · apply WP.spec_mono (body128_msb_spec poly v i ⟨hi0, hlt⟩)
      intro out hout
      obtain ⟨j, rfl, hj⟩ := hout
      simp only
      have hrem : 8 - i.val.toNat = (8-j.val.toNat)+1 := by omega
      refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
      rw [hrem, run128] at hr
      exact hr
    · unfold util.crc128_loop1.body
      simp only [IScalar.lt_equiv, IScalar.ofInt_val_eq, hlt, ↓reduceIte,
        WP.spec_ok]
      have heq : i.val.toNat = 8 := by omega
      simpa only [heq, Nat.sub_self, run128] using hr
  · simp [IScalar.ofInt_val_eq]


def kernel128 (poly : U128) (reflect : Bool) (value : U128) : U128 :=
  run128 poly reflect 8 (if reflect then value else UScalar.mk (ty := .U128) (value.bv <<< 120))

theorem crc128_spec (poly value : U128) (reflect : Bool) :
    WP.spec (util.crc128 poly reflect value) (fun out => out = kernel128 poly reflect value) := by
  unfold util.crc128
  cases reflect with
  | true => exact loop128_ref_spec poly value
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    step
    have heq : value1 = UScalar.mk (ty := .U128) (value.bv <<< 120) := by
      apply (UScalar.eq_equiv_bv_eq _ _).mpr
      exact value1_post1
    subst heq
    exact loop128_msb_spec poly _

theorem lowBit_mul {n : Nat} (x p : BitVec n) :
    (x &&& 1) * p = if x.getLsbD 0 then p else 0 := by
  have h := BitVec.and_one_eq_setWidth_ofBool_getLsbD (x := x)
  calc
    (x &&& 1) * p = ((BitVec.ofBool (x.getLsbD 0)).setWidth n) * p := congrArg (fun a => a * p) h
    _ = _ := by cases hb : x.getLsbD 0 <;> simp [BitVec.ofBool, BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (v := 1) (w := n) (by decide)]

theorem step16_polynomial (poly value : U16) (reflect : Bool) :
    (step16 poly value reflect).bv = polynomialStep poly.bv value.bv reflect := by
  cases reflect with
  | true => exact congrArg (fun a : BitVec 16 => (value.bv >>> 1) ^^^ a) (lowBit_mul value.bv poly.bv)
  | false =>
    have h := lowBit_mul (value.bv >>> 15) poly.bv
    have heq : (value.bv >>> 15).getLsbD 0 = value.bv.getLsbD 15 := by simp
    have h' : ((value.bv >>> 15) &&& (1 : BitVec 16)) * poly.bv =
        if value.bv.getLsbD 15 then poly.bv else 0 := h.trans (by rw [heq])
    exact congrArg (fun a : BitVec 16 => (value.bv <<< 1) ^^^ a) h'
theorem step32_polynomial (poly value : U32) (reflect : Bool) :
    (step32 poly value reflect).bv = polynomialStep poly.bv value.bv reflect := by
  cases reflect with
  | true => exact congrArg (fun a : BitVec 32 => (value.bv >>> 1) ^^^ a) (lowBit_mul value.bv poly.bv)
  | false =>
    have h := lowBit_mul (value.bv >>> 31) poly.bv
    have heq : (value.bv >>> 31).getLsbD 0 = value.bv.getLsbD 31 := by simp
    have h' : ((value.bv >>> 31) &&& (1 : BitVec 32)) * poly.bv =
        if value.bv.getLsbD 31 then poly.bv else 0 := h.trans (by rw [heq])
    exact congrArg (fun a : BitVec 32 => (value.bv <<< 1) ^^^ a) h'
theorem step64_polynomial (poly value : U64) (reflect : Bool) :
    (step64 poly value reflect).bv = polynomialStep poly.bv value.bv reflect := by
  cases reflect with
  | true => exact congrArg (fun a : BitVec 64 => (value.bv >>> 1) ^^^ a) (lowBit_mul value.bv poly.bv)
  | false =>
    have h := lowBit_mul (value.bv >>> 63) poly.bv
    have heq : (value.bv >>> 63).getLsbD 0 = value.bv.getLsbD 63 := by simp
    have h' : ((value.bv >>> 63) &&& (1 : BitVec 64)) * poly.bv =
        if value.bv.getLsbD 63 then poly.bv else 0 := h.trans (by rw [heq])
    exact congrArg (fun a : BitVec 64 => (value.bv <<< 1) ^^^ a) h'
theorem step128_polynomial (poly value : U128) (reflect : Bool) :
    (step128 poly value reflect).bv = polynomialStep poly.bv value.bv reflect := by
  cases reflect with
  | true => exact congrArg (fun a : BitVec 128 => (value.bv >>> 1) ^^^ a) (lowBit_mul value.bv poly.bv)
  | false =>
    have h := lowBit_mul (value.bv >>> 127) poly.bv
    have heq : (value.bv >>> 127).getLsbD 0 = value.bv.getLsbD 127 := by simp
    have h' : ((value.bv >>> 127) &&& (1 : BitVec 128)) * poly.bv =
        if value.bv.getLsbD 127 then poly.bv else 0 := h.trans (by rw [heq])
    exact congrArg (fun a : BitVec 128 => (value.bv <<< 1) ^^^ a) h'

theorem run16_polynomial (poly value : U16) (reflect : Bool) (k : Nat) :
    (run16 poly reflect k value).bv = polynomialRun poly.bv reflect k value.bv := by
  induction k generalizing value with
  | zero => rfl
  | succ k ih =>
    exact (ih (step16 poly value reflect)).trans
      (congrArg (polynomialRun poly.bv reflect k) (step16_polynomial poly value reflect))

theorem crc16_polynomial_spec (poly value : U16) (reflect : Bool) :
    ∃ out, util.crc16 poly reflect value = .ok out ∧
      out.bv = polynomialRun poly.bv reflect 8
        (if reflect then value.bv else value.bv <<< 8) := by
  obtain ⟨out, hout, hmodel⟩ := total_result (crc16_spec poly value reflect)
  refine ⟨out, hout, ?_⟩
  subst out
  unfold kernel16
  exact (run16_polynomial poly _ reflect 8).trans (by cases reflect <;> rfl)

theorem run32_polynomial (poly value : U32) (reflect : Bool) (k : Nat) :
    (run32 poly reflect k value).bv = polynomialRun poly.bv reflect k value.bv := by
  induction k generalizing value with
  | zero => rfl
  | succ k ih =>
    exact (ih (step32 poly value reflect)).trans
      (congrArg (polynomialRun poly.bv reflect k) (step32_polynomial poly value reflect))

theorem crc32_polynomial_spec (poly value : U32) (reflect : Bool) :
    ∃ out, util.crc32 poly reflect value = .ok out ∧
      out.bv = polynomialRun poly.bv reflect 8
        (if reflect then value.bv else value.bv <<< 24) := by
  obtain ⟨out, hout, hmodel⟩ := total_result (crc32_spec poly value reflect)
  refine ⟨out, hout, ?_⟩
  subst out
  unfold kernel32
  exact (run32_polynomial poly _ reflect 8).trans (by cases reflect <;> rfl)

theorem run64_polynomial (poly value : U64) (reflect : Bool) (k : Nat) :
    (run64 poly reflect k value).bv = polynomialRun poly.bv reflect k value.bv := by
  induction k generalizing value with
  | zero => rfl
  | succ k ih =>
    exact (ih (step64 poly value reflect)).trans
      (congrArg (polynomialRun poly.bv reflect k) (step64_polynomial poly value reflect))

theorem crc64_polynomial_spec (poly value : U64) (reflect : Bool) :
    ∃ out, util.crc64 poly reflect value = .ok out ∧
      out.bv = polynomialRun poly.bv reflect 8
        (if reflect then value.bv else value.bv <<< 56) := by
  obtain ⟨out, hout, hmodel⟩ := total_result (crc64_spec poly value reflect)
  refine ⟨out, hout, ?_⟩
  subst out
  unfold kernel64
  exact (run64_polynomial poly _ reflect 8).trans (by cases reflect <;> rfl)

theorem run128_polynomial (poly value : U128) (reflect : Bool) (k : Nat) :
    (run128 poly reflect k value).bv = polynomialRun poly.bv reflect k value.bv := by
  induction k generalizing value with
  | zero => rfl
  | succ k ih =>
    exact (ih (step128 poly value reflect)).trans
      (congrArg (polynomialRun poly.bv reflect k) (step128_polynomial poly value reflect))

theorem crc128_polynomial_spec (poly value : U128) (reflect : Bool) :
    ∃ out, util.crc128 poly reflect value = .ok out ∧
      out.bv = polynomialRun poly.bv reflect 8
        (if reflect then value.bv else value.bv <<< 120) := by
  obtain ⟨out, hout, hmodel⟩ := total_result (crc128_spec poly value reflect)
  refine ⟨out, hout, ?_⟩
  subst out
  unfold kernel128
  exact (run128_polynomial poly _ reflect 8).trans (by cases reflect <;> rfl)
end crc
