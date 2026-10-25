import BytesNumeric
import Proofs.VariableReads
import Proofs.BufferLaws
open Aeneas Aeneas.Std Result
namespace bytes_numeric
abbrev sliceGetI8 := Shared0SliceU8.Insts.BytesBufBuf_implBuf.get_i8
abbrev sliceTryGetI8 := Shared0SliceU8.Insts.BytesBufBuf_implBuf.try_get_i8
abbrev sliceGetU8 := Shared0SliceU8.Insts.BytesBufBuf_implBuf.get_u8
abbrev sliceTryGetU8 := Shared0SliceU8.Insts.BytesBufBuf_implBuf.try_get_u8

private theorem slice_advance_one (s : Slice U8) (hn : 0 < s.val.length) :
    Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance s 1#usize
      ⦃ out => out.val = s.val.drop 1 ⦄ := by
  unfold Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance
  dsimp only
  split
  · scalar_tac
  · step
    simp_all

theorem slice_get_i8_spec (s : Slice U8) (x : U8) (xs : List U8)
    (hs : s.val = x::xs) :
    ∃ out, sliceGetI8 s = .ok out ∧ out.1.val = signed8 x.val ∧ out.2.val = xs := by
  apply bytes_buffers.wp_success
  unfold sliceGetI8 Shared0SliceU8.Insts.BytesBufBuf_implBuf.get_i8
    Mut0T.Insts.BytesBufBuf_implBuf.remaining Mut0T.Insts.BytesBufBuf_implBuf.chunk
    Shared0SliceU8.Insts.BytesBufBuf_implBuf
    Shared0SliceU8.Insts.BytesBufBuf_implBuf.remaining
    Shared0SliceU8.Insts.BytesBufBuf_implBuf.chunk
  dsimp only
  simp only [bind_ok]
  split
  · scalar_tac
  · step
    step
    step with slice_advance_one
    simp_all [cast_i8_value]

theorem slice_try_get_i8_success (s : Slice U8) (x : U8) (xs : List U8)
    (hs : s.val = x::xs) :
    ∃ v out, sliceTryGetI8 s = .ok (.Ok v,out) ∧ v.val = signed8 x.val ∧ out.val = xs := by
  obtain ⟨out,ho,hp⟩ : ∃ out, sliceTryGetI8 s = .ok out ∧
      (∃ v, out.1 = .Ok v ∧ v.val = signed8 x.val) ∧ out.2.val = xs := by
    apply bytes_buffers.wp_success
    unfold sliceTryGetI8 Shared0SliceU8.Insts.BytesBufBuf_implBuf.try_get_i8
      Mut0T.Insts.BytesBufBuf_implBuf.remaining Mut0T.Insts.BytesBufBuf_implBuf.chunk
      Shared0SliceU8.Insts.BytesBufBuf_implBuf
      Shared0SliceU8.Insts.BytesBufBuf_implBuf.remaining
      Shared0SliceU8.Insts.BytesBufBuf_implBuf.chunk
    dsimp only
    simp only [bind_ok]
    split
    · scalar_tac
    · step
      step
      step with slice_advance_one
      simp_all [cast_i8_value]
  obtain ⟨⟨v,hv,hval⟩,htail⟩ := hp
  have hout : out = (.Ok v,out.2) := Prod.ext hv rfl
  exact ⟨v,out.2,hout ▸ ho,hval,htail⟩
theorem slice_try_get_i8_empty (s : Slice U8) (hs : s.val = []) :
    sliceTryGetI8 s = .ok (.Err {requested := 1#usize,available := 0#usize},s) := by
  unfold sliceTryGetI8 Shared0SliceU8.Insts.BytesBufBuf_implBuf.try_get_i8
    Mut0T.Insts.BytesBufBuf_implBuf.remaining
    Shared0SliceU8.Insts.BytesBufBuf_implBuf
    Shared0SliceU8.Insts.BytesBufBuf_implBuf.remaining
  dsimp only
  simp only [bind_ok]
  have hz : Slice.len s = 0#usize := by scalar_tac
  simp [hz]

theorem slice_get_u8_spec (s : Slice U8) (x : U8) (xs : List U8)
    (hs : s.val = x::xs) :
    ∃ out, sliceGetU8 s = .ok out ∧ out.1 = x ∧ out.2.val = xs := by
  apply bytes_buffers.wp_success
  unfold sliceGetU8 Shared0SliceU8.Insts.BytesBufBuf_implBuf.get_u8
    Mut0T.Insts.BytesBufBuf_implBuf.remaining Mut0T.Insts.BytesBufBuf_implBuf.chunk
    Shared0SliceU8.Insts.BytesBufBuf_implBuf
    Shared0SliceU8.Insts.BytesBufBuf_implBuf.remaining
    Shared0SliceU8.Insts.BytesBufBuf_implBuf.chunk
  dsimp only
  simp only [bind_ok]
  split
  · scalar_tac
  · step
    step with slice_advance_one
    simp_all

theorem slice_try_get_u8_success (s : Slice U8) (x : U8) (xs : List U8)
    (hs : s.val = x::xs) :
    ∃ v out, sliceTryGetU8 s = .ok (.Ok v,out) ∧ v = x ∧ out.val = xs := by
  obtain ⟨out,ho,hp⟩ : ∃ out, sliceTryGetU8 s = .ok out ∧
      (∃ v, out.1 = .Ok v ∧ v = x) ∧ out.2.val = xs := by
    apply bytes_buffers.wp_success
    unfold sliceTryGetU8 Shared0SliceU8.Insts.BytesBufBuf_implBuf.try_get_u8
      Mut0T.Insts.BytesBufBuf_implBuf.remaining Mut0T.Insts.BytesBufBuf_implBuf.chunk
      Shared0SliceU8.Insts.BytesBufBuf_implBuf
      Shared0SliceU8.Insts.BytesBufBuf_implBuf.remaining
      Shared0SliceU8.Insts.BytesBufBuf_implBuf.chunk
    dsimp only
    simp only [bind_ok]
    split
    · scalar_tac
    · step
      step with slice_advance_one
      simp_all
  obtain ⟨⟨v,hv,hval⟩,htail⟩ := hp
  have hout : out = (.Ok v,out.2) := Prod.ext hv rfl
  exact ⟨v,out.2,hout ▸ ho,hval,htail⟩
theorem slice_try_get_u8_empty (s : Slice U8) (hs : s.val = []) :
    sliceTryGetU8 s = .ok (.Err {requested := 1#usize,available := 0#usize},s) := by
  unfold sliceTryGetU8 Shared0SliceU8.Insts.BytesBufBuf_implBuf.try_get_u8
    Mut0T.Insts.BytesBufBuf_implBuf.remaining
    Shared0SliceU8.Insts.BytesBufBuf_implBuf
    Shared0SliceU8.Insts.BytesBufBuf_implBuf.remaining
  dsimp only
  simp only [bind_ok]
  have hz : Slice.len s = 0#usize := by scalar_tac
  simp [hz]


private theorem panic_advance_eq_fail (err : bytes.TryGetError) :
    bytes.panic_advance err = .fail .panic := by
  simp only [bytes.panic_advance,core.fmt.rt.Argument.new_display_without_dictionary,core.fmt.Arguments.new]
  unfold core.fmt.rt.Argument core.fmt.Arguments
  rw [bind_ok,bind_ok,bind_ok]

theorem slice_get_i8_empty (s : Slice U8) (hs : s.val = []) :
    sliceGetI8 s = .fail .panic := by
  unfold sliceGetI8 Shared0SliceU8.Insts.BytesBufBuf_implBuf.get_i8
    Mut0T.Insts.BytesBufBuf_implBuf.remaining
    Shared0SliceU8.Insts.BytesBufBuf_implBuf
    Shared0SliceU8.Insts.BytesBufBuf_implBuf.remaining
  dsimp only
  simp only [bind_ok]
  have hz : Slice.len s = 0#usize := by scalar_tac
  simp [hz,panic_advance_eq_fail]

theorem slice_get_u8_empty (s : Slice U8) (hs : s.val = []) :
    sliceGetU8 s = .fail .panic := by
  unfold sliceGetU8 Shared0SliceU8.Insts.BytesBufBuf_implBuf.get_u8
    Mut0T.Insts.BytesBufBuf_implBuf.remaining
    Shared0SliceU8.Insts.BytesBufBuf_implBuf
    Shared0SliceU8.Insts.BytesBufBuf_implBuf.remaining
  dsimp only
  simp only [bind_ok]
  have hz : Slice.len s = 0#usize := by scalar_tac
  simp [hz,panic_advance_eq_fail]

theorem slice_try_get_i8_spec (s : Slice U8) :
    ∃ out, sliceTryGetI8 s = .ok out ∧
      match s.val with
      | [] => out.1 = .Err {requested := 1#usize,available := 0#usize} ∧ out.2 = s
      | x::xs => ∃ v, out.1 = .Ok v ∧ v.val = signed8 x.val ∧ out.2.val = xs := by
  cases hs : s.val with
  | nil => exact ⟨(_,s),slice_try_get_i8_empty s hs,by simp⟩
  | cons x xs =>
    obtain ⟨v,out,ho,hv,ht⟩ := slice_try_get_i8_success s x xs hs
    exact ⟨(.Ok v,out),ho,v,rfl,hv,ht⟩

theorem slice_try_get_u8_spec (s : Slice U8) :
    ∃ out, sliceTryGetU8 s = .ok out ∧
      match s.val with
      | [] => out.1 = .Err {requested := 1#usize,available := 0#usize} ∧ out.2 = s
      | x::xs => out.1 = .Ok x ∧ out.2.val = xs := by
  cases hs : s.val with
  | nil => exact ⟨(_,s),slice_try_get_u8_empty s hs,by simp⟩
  | cons x xs =>
    obtain ⟨v,out,ho,hv,ht⟩ := slice_try_get_u8_success s x xs hs
    exact ⟨(.Ok v,out),ho,by simp [hv],ht⟩

end bytes_numeric
