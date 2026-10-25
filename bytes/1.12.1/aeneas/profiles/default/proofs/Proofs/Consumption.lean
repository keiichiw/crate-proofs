import BytesConsumption
open Aeneas Aeneas.Std Result
namespace bytes_consumption
private theorem wp_to_success {α : Type _} {m : Result α} {p : α → Prop}
    (h : WP.spec m p) : ∃ out, m = .ok out ∧ p out := by
  cases m using Result.cases with
  | ret x => exact ⟨x, rfl, (WP.spec_ok x).mp h⟩
  | vis effect k => exact False.elim ((WP.spec_vis effect k).mp h)
  | div => exact False.elim (WP.spec_div.mp h)

@[step] theorem slice_advance_wp (s : Slice U8) (n : Usize) (hn : n.val ≤ s.val.length) :
    Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance s n
      ⦃out => out.val = s.val.drop n.val ∧ out.val.length = s.val.length - n.val⦄ := by
  unfold Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance
  dsimp only
  split
  · scalar_tac
  · step
    simp_all

theorem slice_advance_spec (s : Slice U8) (n : Usize) (hn : n.val ≤ s.val.length) :
    ∃ out, Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance s n = .ok out ∧
      out.val = s.val.drop n.val ∧ out.val.length = s.val.length - n.val := by
  exact wp_to_success (slice_advance_wp s n hn)

theorem slice_copy_spec (s d : Slice U8) (hn : d.val.length ≤ s.val.length) :
    ∃ out, Shared0SliceU8.Insts.BytesBufBuf_implBuf.copy_to_slice s d = .ok out ∧
      out.1.val = s.val.drop d.val.length ∧ out.2.val = s.val.take d.val.length ∧
      out.1.val.length = s.val.length - d.val.length ∧ out.2.val.length = d.val.length := by
  apply wp_to_success
  unfold Shared0SliceU8.Insts.BytesBufBuf_implBuf.copy_to_slice
  dsimp only
  split
  · scalar_tac
  · step
    step
    step
    simp_all [Slice.len,Slice.length]

theorem panic_advance_eq_fail (err : bytes.TryGetError) :
    bytes.panic_advance err = .fail .panic := by
  simp only [bytes.panic_advance,core.fmt.rt.Argument.new_display_without_dictionary,core.fmt.Arguments.new]
  unfold core.fmt.rt.Argument core.fmt.Arguments
  rw [bind_ok,bind_ok,bind_ok]

theorem slice_advance_invalid (s : Slice U8) (n : Usize) (hn : s.val.length < n.val) :
    Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance s n = .fail .panic := by
  unfold Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance
  dsimp only
  have hlt : Slice.len s < n := by scalar_tac
  rw [ite_eq_left hlt,panic_advance_eq_fail]
  simp

theorem slice_copy_invalid (s d : Slice U8) (hn : s.val.length < d.val.length) :
    Shared0SliceU8.Insts.BytesBufBuf_implBuf.copy_to_slice s d = .fail .panic := by
  unfold Shared0SliceU8.Insts.BytesBufBuf_implBuf.copy_to_slice
  dsimp only
  have hlt : Slice.len s < Slice.len d := by scalar_tac
  rw [ite_eq_left hlt,panic_advance_eq_fail]
  simp

theorem slice_advance_sequence (s : Slice U8) (n m : Usize)
    (hfit : n.val + m.val ≤ s.val.length) :
    ∃ out, (do
      let intermediate ← Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance s n
      Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance intermediate m) = .ok out ∧
      out.val = s.val.drop (n.val+m.val) ∧
      out.val.length = s.val.length - (n.val+m.val) := by
  apply wp_to_success
  step
  step
  all_goals simp_all [List.drop_drop]
  all_goals omega
end bytes_consumption
