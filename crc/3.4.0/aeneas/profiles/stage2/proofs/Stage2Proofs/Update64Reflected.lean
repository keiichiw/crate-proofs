import CrcBody.Funs
import Stage2Proofs.ByteMath
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace CrcUpdate64Reflected
abbrev Table := Array (Array U64 256#usize) 1#usize

def indexWord (state : U64) (byte : U8) : U64 :=
  ⟨(state.bv ^^^ byte.bv.setWidth 64) &&& (255 : BitVec 64)⟩

theorem indexWord_bound (state : U64) (byte : U8) : (indexWord state byte).val < 256 := by
  have h : (indexWord state byte).val ≤ 255 := by
    change (((state.bv ^^^ byte.bv.setWidth 64).toNat) &&& 255) ≤ 255
    exact Nat.and_le_right
  omega

theorem cast_index (x : U64) (hx : x.val < 256) :
    (UScalar.cast .Usize x).val = x.val := by
  simp only [UScalar.cast_val_eq]
  cases System.Platform.numBits_eq <;> simp [*] <;> scalar_tac

def lookup (table : Table) (state : U64) (byte : U8) : U64 :=
  table.val[0].val[(indexWord state byte).val]! ^^^
    (⟨state.bv >>> 8⟩ : U64)

def run (table : Table) (state : U64) (bytes : List U8) : U64 :=
  bytes.foldl (lookup table) state

theorem body_spec (table : Table) (bytes : Slice U8) (state : U64) (i : Usize)
    (hi : i.val < bytes.val.length) :
    WP.spec (CrcBody.crc64.update_table_loop5.body table bytes (Slice.len bytes) state i)
      (fun out => ∃ j, out = .cont (lookup table state bytes.val[i.val], j) ∧
        j.val = i.val + 1) := by
  unfold CrcBody.crc64.update_table_loop5.body
  simp only [UScalar.lt_equiv, Slice.len_val, hi, ↓reduceIte]
  step
  step
  step
  step
  step
  step
  step
  · have hb : i4.val ≤ 255 := by
      simpa [i4_post, UScalar.val_and] using (Nat.and_le_right : i3.val &&& 255 ≤ 255)
    have hc : table_index.val = i4.val := by
      rw [table_index_post]
      exact cast_index _ (by omega)
    scalar_tac
  step
  step
  step
  refine ⟨i7, ?_, i7_post⟩
  congr 1
  congr 1
  have hindex : indexWord state bytes.val[i.val] = i4 := by
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    rw [i4_post1, i3_post1, i2_post, i1_post]
    rfl
  have hidx : table_index.val = i4.val := by
    rw [table_index_post]
    apply cast_index
    rw [← hindex]
    exact indexWord_bound _ _
  unfold lookup
  rw [hindex]
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  have hi4 : i4.val < table.val[0].val.length := by simpa [← hindex] using indexWord_bound state bytes.val[i.val]
  simpa only [UScalar.bv_xor, i5_post, a_post, hidx, i6_post1, UScalar.bv_mk,
    List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi4, Option.getD_some] using crc1_post1

theorem loop_spec (table : Table) (bytes : Slice U8) (initial : U64) :
    WP.spec (CrcBody.crc64.update_table_loop5 initial table bytes (Slice.len bytes) 0#usize)
      (fun out => out = run table initial bytes.val) := by
  unfold CrcBody.crc64.update_table_loop5
  apply loop.spec_decr_nat
    (measure := fun x : U64 × Usize => bytes.val.length - x.2.val)
    (inv := fun x : U64 × Usize => x.2.val ≤ bytes.val.length ∧
      run table x.1 (bytes.val.drop x.2.val) = run table initial bytes.val)
  · intro x hx
    rcases x with ⟨state, i⟩
    dsimp only at hx
    obtain ⟨hi, hr⟩ := hx
    by_cases hlt : i.val < bytes.val.length
    · apply WP.spec_mono (body_spec table bytes state i hlt)
      intro out hout
      obtain ⟨j, rfl, hj⟩ := hout
      simp only
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [List.drop_eq_getElem_cons hlt] at hr
      simpa only [run, List.foldl_cons, hj] using hr
    · unfold CrcBody.crc64.update_table_loop5.body
      simp only [UScalar.lt_equiv, Slice.len_val, hlt, ↓reduceIte, WP.spec_ok]
      have heq : i.val = bytes.val.length := by omega
      simpa [run, heq] using hr
  · simp

theorem update_table_total (algorithm : CrcBody.crc_catalog.Algorithm U64)
    (table : Table) (bytes : Slice U8) (initial : U64) (href : algorithm.refin = true) :
    ∃ out, CrcBody.crc64.update_table initial algorithm table bytes = .ok out ∧
      out = run table initial bytes.val := by
  apply crc.total_result
  unfold CrcBody.crc64.update_table
  simp only [show (1#usize : Usize) ≠ 16#usize by decide, ↓reduceIte,
    show (1#usize : Usize) > 0#usize by decide, href]
  exact loop_spec table bytes initial


theorem digest_update_total
    (self : CrcBody.Digest U64 (CrcBody.Table 1#usize) Table) (bytes : Slice U8)
    (href : self.crc.algorithm.refin = true) :
    ∃ out, CrcBody.crc64.DigestAU64Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value = run self.crc.data self.value bytes.val := by
  obtain ⟨value, hvalue, hrun⟩ := update_table_total self.crc.algorithm self.crc.data bytes self.value href
  unfold CrcBody.crc64.DigestAU64Table.update CrcBody.crc64.CrcU64Table.update
  rw [hvalue]
  simp only [bind_ok]
  exact ⟨{ self with value := value }, rfl, rfl, hrun⟩

end CrcUpdate64Reflected
