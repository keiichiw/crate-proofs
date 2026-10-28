import IntegerCore
import VarintSpec
import Zigzag
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace IntegerRequiredSpace
open IntegerEncodingSpec

def remaining (n : Nat) : Nat := if n = 0 then 0 else uLen n

theorem remaining_pos {n : Nat} (h : 0 < n) : 1 ≤ remaining n := by
  simpa [remaining, Nat.ne_of_gt h] using uLen_pos n

theorem remaining_step {n : Nat} (h : 0 < n) : remaining n = remaining (n/128) + 1 := by
  by_cases hs : n < 128
  · have hd : n/128 = 0 := Nat.div_eq_of_lt hs
    simp [remaining, hd, Nat.ne_of_gt h, uLen_small hs]
  · have hn : 128 ≤ n := by omega
    have hd : 0 < n/128 := Nat.div_pos hn (by decide)
    simp only [remaining, Nat.ne_of_gt h, Nat.ne_of_gt hd, ↓reduceIte]
    exact uLen_step hn

theorem total_result {α : Type _} {m : Result α} {p : α → Prop}
    (h : WP.spec m p) : ∃ value, m = Result.ok value ∧ p value := by
  cases m using Result.cases with
  | ret value => exact ⟨value, rfl, WP.spec_ok value |>.mp h⟩
  | vis effect k => exact False.elim ((WP.spec_vis effect k).mp h)
  | div => exact False.elim (WP.spec_div.mp h)

theorem loop_spec (v : U64) (counter : Usize)
    (hb : counter.val + remaining v.val ≤ 10) :
    WP.spec (integer_encoding.varint.required_encoded_space_unsigned_loop v counter)
      (fun out => out.val = counter.val + remaining v.val) := by
  unfold integer_encoding.varint.required_encoded_space_unsigned_loop
  apply loop.spec_decr_nat
    (measure := fun x : U64 × Usize => x.1.val)
    (inv := fun x : U64 × Usize => x.2.val + remaining x.1.val = counter.val + remaining v.val)
  · intro x hx
    rcases x with ⟨value,c⟩
    dsimp only at hx
    unfold integer_encoding.varint.required_encoded_space_unsigned_loop.body
    by_cases hp : 0 < value.val
    · simp only [UScalar.lt_equiv, show (0#u64 : U64).val = 0 by rfl, hp, ↓reduceIte]
      have hr := remaining_pos hp
      step
      step
      have hd : v1.val = value.val / 128 := by
        simpa [Nat.shiftRight_eq_div_pow] using v1_post
      refine ⟨?_, ?_⟩
      · rw [logcounter1_post, hd]
        have hs := remaining_step hp
        omega
      · rw [hd]
        exact Nat.div_lt_self hp (by decide)
    · simp only [UScalar.lt_equiv, show (0#u64 : U64).val = 0 by rfl, hp, ↓reduceIte, WP.spec_ok]
      have hz : value.val = 0 := by omega
      simpa [remaining, hz] using hx
  · rfl

theorem unsigned_total (v : U64) :
    ∃ out, integer_encoding.varint.required_encoded_space_unsigned v = .ok out ∧ out.val = uLen v.val := by
  unfold integer_encoding.varint.required_encoded_space_unsigned
  by_cases hv : v = 0#u64
  · subst v
    exact ⟨1#usize, by simp, by simp [uLen, Nat.log_zero_right]⟩
  · simp only [hv, ↓reduceIte]
    have hn : v.val ≠ 0 := by intro h; apply hv; exact UScalar.eq_of_val_eq h
    have hb : (0#usize : Usize).val + remaining v.val ≤ 10 := by
      have hm := v.hmax
      simpa [remaining, hn] using (uLen_le10 hm)
    obtain ⟨out, ho, hval⟩ := total_result (loop_spec v 0#usize hb)
    exact ⟨out, ho, by simpa [remaining, hn] using hval⟩


theorem signed_total (v : I64) :
    ∃ out, integer_encoding.varint.required_encoded_space_signed v = .ok out ∧
      out.val = uLen (zigzag v.val) := by
  obtain ⟨z, hz, hzb⟩ := integer_encoding.zigzag_encode_spec v
  obtain ⟨out, ho, hov⟩ := unsigned_total z
  refine ⟨out, ?_, ?_⟩
  · simp [integer_encoding.varint.required_encoded_space_signed, hz, ho]
  · simpa [hzb] using hov

theorem u8_required_space (v : U8) :
    ∃ out, integer_encoding.U8.Insts.Integer_encodingVarintVarInt.required_space v = .ok out ∧
      out.val = uLen v.val := by
  unfold integer_encoding.U8.Insts.Integer_encodingVarintVarInt.required_space
  apply total_result
  step
  obtain ⟨out, ho, hov⟩ := unsigned_total i
  rw [ho]
  apply (WP.spec_ok out).mpr
  simpa [i_post] using hov

theorem u16_required_space (v : U16) :
    ∃ out, integer_encoding.U16.Insts.Integer_encodingVarintVarInt.required_space v = .ok out ∧
      out.val = uLen v.val := by
  unfold integer_encoding.U16.Insts.Integer_encodingVarintVarInt.required_space
  apply total_result
  step
  obtain ⟨out, ho, hov⟩ := unsigned_total i
  rw [ho]
  apply (WP.spec_ok out).mpr
  simpa [i_post] using hov

theorem u32_required_space (v : U32) :
    ∃ out, integer_encoding.U32.Insts.Integer_encodingVarintVarInt.required_space v = .ok out ∧
      out.val = uLen v.val := by
  unfold integer_encoding.U32.Insts.Integer_encodingVarintVarInt.required_space
  apply total_result
  step
  obtain ⟨out, ho, hov⟩ := unsigned_total i
  rw [ho]
  apply (WP.spec_ok out).mpr
  simpa [i_post] using hov

theorem u64_required_space (v : U64) :
    ∃ out, integer_encoding.U64.Insts.Integer_encodingVarintVarInt.required_space v = .ok out ∧
      out.val = uLen v.val := by
  unfold integer_encoding.U64.Insts.Integer_encodingVarintVarInt.required_space
  exact unsigned_total v

theorem usize_required_space (v : Usize) :
    ∃ out, integer_encoding.Usize.Insts.Integer_encodingVarintVarInt.required_space v = .ok out ∧
      out.val = uLen v.val := by
  unfold integer_encoding.Usize.Insts.Integer_encodingVarintVarInt.required_space
  apply total_result
  step
  obtain ⟨out, ho, hov⟩ := unsigned_total i
  rw [ho]
  apply (WP.spec_ok out).mpr
  simpa [i_post] using hov

theorem i8_required_space (v : I8) :
    ∃ out, integer_encoding.I8.Insts.Integer_encodingVarintVarInt.required_space v = .ok out ∧
      out.val = uLen (zigzag v.val) := by
  unfold integer_encoding.I8.Insts.Integer_encodingVarintVarInt.required_space
  apply total_result
  step
  obtain ⟨out, ho, hov⟩ := signed_total i
  rw [ho]
  apply (WP.spec_ok out).mpr
  simpa [i_post] using hov

theorem i16_required_space (v : I16) :
    ∃ out, integer_encoding.I16.Insts.Integer_encodingVarintVarInt.required_space v = .ok out ∧
      out.val = uLen (zigzag v.val) := by
  unfold integer_encoding.I16.Insts.Integer_encodingVarintVarInt.required_space
  apply total_result
  step
  obtain ⟨out, ho, hov⟩ := signed_total i
  rw [ho]
  apply (WP.spec_ok out).mpr
  simpa [i_post] using hov

theorem i32_required_space (v : I32) :
    ∃ out, integer_encoding.I32.Insts.Integer_encodingVarintVarInt.required_space v = .ok out ∧
      out.val = uLen (zigzag v.val) := by
  unfold integer_encoding.I32.Insts.Integer_encodingVarintVarInt.required_space
  apply total_result
  step
  obtain ⟨out, ho, hov⟩ := signed_total i
  rw [ho]
  apply (WP.spec_ok out).mpr
  simpa [i_post] using hov

theorem i64_required_space (v : I64) :
    ∃ out, integer_encoding.I64.Insts.Integer_encodingVarintVarInt.required_space v = .ok out ∧
      out.val = uLen (zigzag v.val) := by
  unfold integer_encoding.I64.Insts.Integer_encodingVarintVarInt.required_space
  exact signed_total v

theorem isize_required_space (v : Isize) :
    ∃ out, integer_encoding.Isize.Insts.Integer_encodingVarintVarInt.required_space v = .ok out ∧
      out.val = uLen (zigzag v.val) := by
  unfold integer_encoding.Isize.Insts.Integer_encodingVarintVarInt.required_space
  apply total_result
  step
  obtain ⟨out, ho, hov⟩ := signed_total i
  rw [ho]
  apply (WP.spec_ok out).mpr
  simpa [i_post] using hov

end IntegerRequiredSpace
