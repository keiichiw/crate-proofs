import CrcBody.Funs
import Stage2Proofs.ByteMath
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace CrcUpdate8

abbrev Table := Array (Array U8 256#usize) 1#usize

def tableRead (table : Table) (byte : U8) : U8 :=
  table.val[0].val[byte.val]'(by have h := byte.hmax; scalar_tac)

def lookup (table : Table) (state byte : U8) : U8 := tableRead table (state ^^^ byte)

def run (table : Table) (state : U8) (bytes : List U8) : U8 :=
  bytes.foldl (lookup table) state

theorem body_spec (table : Table) (bytes : Slice U8) (state : U8) (i : Usize)
    (hi : i.val < bytes.val.length) :
    WP.spec (CrcBody.crc8.update_table_loop3.body table bytes (Slice.len bytes) state i)
      (fun out => ∃ j, out = .cont (lookup table state bytes.val[i.val], j) ∧
        j.val = i.val + 1) := by
  unfold CrcBody.crc8.update_table_loop3.body
  simp only [UScalar.lt_equiv, Slice.len_val]
  simp only [hi, ↓reduceIte]
  step
  step
  step
  step
  step
  step
  refine ⟨i4, ?_, i4_post⟩
  congr 1
  unfold lookup tableRead
  simp_all

theorem loop_spec (table : Table) (bytes : Slice U8) (initial : U8) :
    WP.spec (CrcBody.crc8.update_table_loop3 initial table bytes (Slice.len bytes) 0#usize)
      (fun out => out = run table initial bytes.val) := by
  unfold CrcBody.crc8.update_table_loop3
  apply loop.spec_decr_nat
    (measure := fun x : U8 × Usize => bytes.val.length - x.2.val)
    (inv := fun x : U8 × Usize => x.2.val ≤ bytes.val.length ∧
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
    · unfold CrcBody.crc8.update_table_loop3.body
      simp only [UScalar.lt_equiv, Slice.len_val, hlt, ↓reduceIte, WP.spec_ok]
      have heq : i.val = bytes.val.length := by omega
      simpa [run, heq] using hr
  · simp

theorem update_table_total (algorithm : CrcBody.crc_catalog.Algorithm U8)
    (table : Table) (bytes : Slice U8) (initial : U8) :
    ∃ out, CrcBody.crc8.update_table initial algorithm table bytes = .ok out ∧
      out = run table initial bytes.val := by
  apply crc.total_result
  unfold CrcBody.crc8.update_table
  simp only [show (1#usize : Usize) ≠ 16#usize by decide, ↓reduceIte,
    show (1#usize : Usize) > 0#usize by decide]
  exact loop_spec table bytes initial


theorem digest_update_total
    (self : CrcBody.Digest U8 (CrcBody.Table 1#usize) Table) (bytes : Slice U8) :
    ∃ out, CrcBody.crc8.DigestAU8Table.update self bytes = .ok out ∧
      out.crc = self.crc ∧ out.value = run self.crc.data self.value bytes.val := by
  obtain ⟨value, hvalue, hrun⟩ := update_table_total self.crc.algorithm self.crc.data bytes self.value
  unfold CrcBody.crc8.DigestAU8Table.update CrcBody.crc8.CrcU8Table.update
  rw [hvalue]
  simp only [bind_ok]
  exact ⟨{ self with value := value }, rfl, rfl, hrun⟩

end CrcUpdate8
