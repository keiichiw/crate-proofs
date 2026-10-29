import CrcBody.Funs
import Stage2Proofs.ByteMathWide
import Stage2Proofs.Public64Base
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace CrcNoTable64

theorem utility_eq (poly value : U64) (reflect : Bool) :
    CrcBody.util.crc64 poly reflect value = crc.util.crc64 poly reflect value := by rfl

@[step] theorem utility_spec (poly value : U64) :
    WP.spec (CrcBody.util.crc64 poly false value)
      (fun out => out.bv = crc.polynomialRun poly.bv false 8 (value.bv <<< 56)) := by
  obtain ⟨out, hout, hv⟩ := crc.crc64_polynomial_spec poly value false
  rw [utility_eq, hout]
  exact (WP.spec_ok out).mpr hv

def step (poly state : U64) (byte : U8) : U64 :=
  UScalar.mk (crc.polynomialRun poly.bv false 8
    ((((state.bv >>> 56) ^^^ byte.bv.setWidth 64) &&& (255 : BitVec 64)) <<< 56) ^^^
      (state.bv <<< 8))

def run (poly initial : U64) (bytes : List U8) : U64 := bytes.foldl (step poly) initial

theorem body_spec (poly : U64) (bytes : Slice U8) (state : U64) (i : Usize)
    (hi : i.val < bytes.val.length) :
    WP.spec (CrcBody.crc64.update_table_loop8.body bytes (Slice.len bytes) false poly state i)
      (fun out => ∃ j, out = .cont (step poly state bytes.val[i.val], j) ∧
        j.val = i.val + 1) := by
  unfold CrcBody.crc64.update_table_loop8.body
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
  apply congrArg (fun v : U64 => ControlFlow.cont (v, i7))
  unfold step
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  simp only [crc1_post1, i5_post, to_crc_post1, i4_post1, i1_post1, i3_post, i2_post,
    i6_post1, UScalar.cast]
  rfl

theorem loop_spec (poly : U64) (bytes : Slice U8) (initial : U64) :
    WP.spec (CrcBody.crc64.update_table_loop8 initial bytes (Slice.len bytes) 0#usize false poly)
      (fun out => out = run poly initial bytes.val) := by
  unfold CrcBody.crc64.update_table_loop8
  apply loop.spec_decr_nat
    (measure := fun x : U64 × Usize => bytes.val.length - x.2.val)
    (inv := fun x : U64 × Usize => x.2.val ≤ bytes.val.length ∧
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
    · unfold CrcBody.crc64.update_table_loop8.body
      simp only [UScalar.lt_equiv, Slice.len_val, hlt, ↓reduceIte, WP.spec_ok]
      have heq : i.val = bytes.val.length := by omega
      simpa [run, heq] using hr
  · simp

theorem update_table_total (algorithm : CrcBody.crc_catalog.Algorithm U64)
    (table : Array (Array U64 256#usize) 0#usize) (bytes : Slice U8) (initial : U64)
    (hw : algorithm.width = 64#u8) (hr : algorithm.refin = false) :
    ∃ out, CrcBody.crc64.update_table initial algorithm table bytes = .ok out ∧
      out = run algorithm.poly initial bytes.val := by
  apply crc.total_result
  unfold CrcBody.crc64.update_table
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

theorem step_canonical (poly state : U64) (byte : U8) :
    (step poly state byte).bv = CrcCanonicalWide.byteStep poly.bv state.bv byte.bv := by
  have hlo : ((state.bv ^^^ (byte.bv.setWidth 64 <<< 56)) <<< 8) = state.bv <<< 8 := by
    rw [BitVec.shiftLeft_xor_distrib, ← BitVec.shiftLeft_add]
    simp
  have hhi : ((state.bv ^^^ (byte.bv.setWidth 64 <<< 56)) >>> 56) <<< 56 =
      (((state.bv >>> 56 ^^^ byte.bv.setWidth 64) &&& 255) <<< 56) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rw [CrcCanonicalWide.byteStep_injection (by decide), CrcCanonicalWide.encodeByte]
  rw [CrcCanonicalWide.polynomialRun_split8 (by decide)]
  change _ = ((state.bv ^^^ (byte.bv.setWidth 64 <<< 56)) <<< 8) ^^^
    crc.polynomialRun poly.bv false 8 (((state.bv ^^^ (byte.bv.setWidth 64 <<< 56)) >>> 56) <<< 56)
  rw [hlo, hhi]
  exact BitVec.xor_comm _ _

theorem run_bv (poly state : U64) (bytes : List U8) :
    (run poly state bytes).bv =
      CrcCanonicalWide.run poly.bv state.bv (bytes.map UScalar.bv) := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte bytes ih =>
    change (run poly (step poly state byte) bytes).bv =
      CrcCanonicalWide.run poly.bv (CrcCanonicalWide.byteStep poly.bv state.bv byte.bv)
        (bytes.map UScalar.bv)
    rw [ih, step_canonical]

abbrev Crc64 := CrcBody.Crc U64 (CrcBody.Table 0#usize) (Array (Array U64 256#usize) 0#usize)
abbrev Digest64 := CrcBody.Digest U64 (CrcBody.Table 0#usize) (Array (Array U64 256#usize) 0#usize)

theorem update64_canonical (self : Crc64) (state : U64) (bytes : Slice U8)
    (hw : self.algorithm.width = 64#u8) (hr : self.algorithm.refin = false) :
    ∃ out, CrcBody.crc64.CrcU64Table.update self state bytes = .ok out ∧
      out.bv = CrcCanonicalWide.run self.algorithm.poly.bv state.bv
        (bytes.val.map UScalar.bv) := by
  obtain ⟨out, hout, hv⟩ := update_table_total self.algorithm self.data bytes state hw hr
  exact ⟨out, hout, (congrArg UScalar.bv hv).trans (run_bv _ _ _)⟩

/-- NoTable update, arbitrary polynomial and messages, full-width nonreflected input. -/
theorem digest64_update_canonical (self : Digest64) (bytes : Slice U8)
    (hw : self.crc.algorithm.width = 64#u8) (hr : self.crc.algorithm.refin = false) :
    ∃ out, CrcBody.crc64.DigestAU64Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value.bv =
        CrcCanonicalWide.run self.crc.algorithm.poly.bv self.value.bv
          (bytes.val.map UScalar.bv) := by
  obtain ⟨mid, hm, hv⟩ := update64_canonical self.crc self.value bytes hw hr
  exact ⟨{self with value := mid}, by simp [CrcBody.crc64.DigestAU64Table.update, hm], rfl, hv⟩

/-- Full-width NoTable checksum, nonreflected input and either output reflection. -/
theorem checksum64_canonical (self : Crc64) (bytes : Slice U8)
    (ha : CrcPublic64.NonRef64 self.algorithm) :
    ∃ out, CrcBody.crc64.CrcU64Table.checksum self bytes = .ok out ∧
      out.bv = (if self.algorithm.refout then
        (CrcCanonicalWide.run self.algorithm.poly.bv self.algorithm.init.bv
          (bytes.val.map UScalar.bv)).reverse else
        CrcCanonicalWide.run self.algorithm.poly.bv self.algorithm.init.bv
          (bytes.val.map UScalar.bv)) ^^^ self.algorithm.xorout.bv := by
  obtain ⟨mid, hm, hv⟩ := update64_canonical self self.algorithm.init bytes ha.1 ha.2
  obtain ⟨out, hout, ho⟩ := CrcPublic64.finalize_total self.algorithm mid ha
  refine ⟨out, ?_, ?_⟩
  · simp only [CrcBody.crc64.CrcU64Table.checksum, CrcPublic64.init_identity _ _ ha,
      hm, bind_ok, hout]
  · simpa only [hv] using ho

theorem digest_protocol_canonical (self : Crc64) (initial : U64) (bytes : Slice U8)
    (ha : CrcPublic64.NonRef64 self.algorithm) :
    ∃ start stop out,
      CrcBody.crc64.CrcU64Table.digest_with_initial self initial = .ok start ∧
      CrcBody.crc64.DigestAU64Table.update start bytes = .ok stop ∧
      CrcBody.crc64.DigestAU64Table.finalize stop = .ok out ∧
      out.bv = (if self.algorithm.refout then
        (CrcCanonicalWide.run self.algorithm.poly.bv initial.bv (bytes.val.map UScalar.bv)).reverse
        else CrcCanonicalWide.run self.algorithm.poly.bv initial.bv (bytes.val.map UScalar.bv))
        ^^^ self.algorithm.xorout.bv := by
  obtain ⟨stop, hu, hc, hv⟩ := digest64_update_canonical (⟨self, initial⟩ : Digest64) bytes ha.1 ha.2
  have hfa : CrcPublic64.NonRef64 stop.crc.algorithm := by simpa only [hc] using ha
  obtain ⟨out, hout, hbv⟩ := CrcPublic64.finalize_total stop.crc.algorithm stop.value hfa
  refine ⟨⟨self, initial⟩, stop, out, ?_, hu, hout, ?_⟩
  · simp only [CrcBody.crc64.CrcU64Table.digest_with_initial, CrcPublic64.init_identity _ _ ha,
      bind_ok, CrcBody.crc64.DigestAU64Table.new]
  · simpa only [hc, hv] using hbv

end CrcNoTable64
