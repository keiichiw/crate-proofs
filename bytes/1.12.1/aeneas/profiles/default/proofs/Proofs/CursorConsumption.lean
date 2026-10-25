import BytesCursorSlice
import Proofs.CursorHelpers
open Aeneas Aeneas.Std Result
namespace bytes_cursor_proofs
abbrev Cursor := bytes_cursor_slice.core.io.cursor.Cursor
abbrev remaining := @bytes_cursor_slice.core.io.cursor.Cursor.Insts.BytesBufBuf_implBuf.remaining
abbrev chunk := @bytes_cursor_slice.core.io.cursor.Cursor.Insts.BytesBufBuf_implBuf.chunk
abbrev advance := @bytes_cursor_slice.core.io.cursor.Cursor.Insts.BytesBufBuf_implBuf.advance

private theorem wp_success {α : Type _} {m : Result α} {p : α → Prop}
    (h : WP.spec m p) : ∃ out, m = .ok out ∧ p out := by
  cases m using Result.cases with
  | ret x => exact ⟨x, rfl, (WP.spec_ok x).mp h⟩
  | vis effect k => exact False.elim ((WP.spec_vis effect k).mp h)
  | div => exact False.elim (WP.spec_div.mp h)

theorem min_bridge (a : U64) (b : Usize) :
    bytes_cursor_slice.bytes.min_u64_usize a b = _root_.bytes.min_u64_usize a b := rfl

theorem sub_bridge (a : Usize) (b : U64) :
    bytes_cursor_slice.bytes.saturating_sub_usize_u64 a b = _root_.bytes.saturating_sub_usize_u64 a b := rfl

theorem cursor_remaining_spec {T} (h64 : System.Platform.numBits = 64)
    (A : core.convert.AsRef T (Slice U8)) (s : Cursor T) (buffer : Slice U8)
    (hA : A.as_ref s.inner = .ok buffer) :
    ∃ out, remaining A s = .ok out ∧ out.val = buffer.val.length - s.pos.val := by
  obtain ⟨out, ho, hv⟩ := _root_.bytes.saturating_sub_usize_u64_spec h64 (Slice.len buffer) s.pos
  refine ⟨out, ?_, ?_⟩
  · simpa [remaining,bytes_cursor_slice.core.io.cursor.Cursor.Insts.BytesBufBuf_implBuf.remaining,
      bytes_cursor_slice.core.io.cursor.Cursor.get_ref,bytes_cursor_slice.core.io.cursor.Cursor.position,hA,sub_bridge] using ho
  · simpa [Slice.len] using hv

theorem cursor_chunk_spec {T} (h64 : System.Platform.numBits = 64)
    (A : core.convert.AsRef T (Slice U8)) (s : Cursor T) (buffer : Slice U8)
    (hA : A.as_ref s.inner = .ok buffer) :
    ∃ out, chunk A s = .ok out ∧ out.val = buffer.val.drop s.pos.val := by
  obtain ⟨pos, hp, hv⟩ := _root_.bytes.min_u64_usize_spec h64 s.pos (Slice.len buffer)
  apply wp_success
  unfold chunk bytes_cursor_slice.core.io.cursor.Cursor.Insts.BytesBufBuf_implBuf.chunk
  simp only [bytes_cursor_slice.core.io.cursor.Cursor.get_ref,bytes_cursor_slice.core.io.cursor.Cursor.position,bind_ok,hA]
  rw [min_bridge,hp,bind_ok]
  step
  simp_all only [Slice.len, Slice.length]
  by_cases h : s.pos.val ≤ buffer.val.length
  · simp [Nat.min_eq_left h]
  · have h' : buffer.val.length ≤ s.pos.val := by omega
    simp_all

theorem cursor_advance_spec {T} (h64 : System.Platform.numBits = 64)
    (A : core.convert.AsRef T (Slice U8)) (s : Cursor T) (buffer : Slice U8)
    (hA : A.as_ref s.inner = .ok buffer) (n : Usize)
    (hn : n.val ≤ buffer.val.length - s.pos.val) :
    ∃ out, advance A s n = .ok out ∧ out.inner = s.inner ∧
      out.pos.val = s.pos.val + n.val := by
  obtain ⟨max_cnt, hm, hv⟩ := _root_.bytes.saturating_sub_usize_u64_spec h64 (Slice.len buffer) s.pos
  have hn' : ¬ n > max_cnt := by
    simp only [Slice.len] at hv
    scalar_tac
  apply wp_success
  unfold advance bytes_cursor_slice.core.io.cursor.Cursor.Insts.BytesBufBuf_implBuf.advance
  simp only [bytes_cursor_slice.core.io.cursor.Cursor.get_ref,bytes_cursor_slice.core.io.cursor.Cursor.position,bind_ok,hA]
  rw [sub_bridge,hm,bind_ok,ite_eq_right hn']
  have hlen := Slice.property buffer
  have hpos := s.pos.hBounds
  have hsum : s.pos.val + n.val ≤ U64.max := by
    simp only [Usize.max,U64.max,U64.numBits,Usize.numBits,UScalarTy.numBits,h64] at *
    omega
  step
  step
  simp_all [bytes_cursor_slice.core.io.cursor.Cursor.set_position,WP.spec_ok]

private def arrayBuffer {N : Usize} (a : Array U8 N) : Slice U8 :=
  Slice.from a.val (by scalar_tac)

theorem array_remaining_spec (h64 : System.Platform.numBits = 64) {N : Usize}
    (s : Cursor (Array U8 N)) :
    ∃ out, remaining (Array.Insts.CoreConvertAsRefSlice U8 N) s = .ok out ∧
      out.val = s.inner.val.length - s.pos.val := by
  simpa [arrayBuffer] using cursor_remaining_spec h64 (Array.Insts.CoreConvertAsRefSlice U8 N) s (arrayBuffer s.inner) rfl

theorem array_chunk_spec (h64 : System.Platform.numBits = 64) {N : Usize}
    (s : Cursor (Array U8 N)) :
    ∃ out, chunk (Array.Insts.CoreConvertAsRefSlice U8 N) s = .ok out ∧
      out.val = s.inner.val.drop s.pos.val := by
  simpa [arrayBuffer] using cursor_chunk_spec h64 (Array.Insts.CoreConvertAsRefSlice U8 N) s (arrayBuffer s.inner) rfl

theorem array_advance_spec (h64 : System.Platform.numBits = 64) {N : Usize}
    (s : Cursor (Array U8 N)) (n : Usize)
    (hn : n.val ≤ s.inner.val.length - s.pos.val) :
    ∃ out, advance (Array.Insts.CoreConvertAsRefSlice U8 N) s n = .ok out ∧
      out.inner = s.inner ∧ out.pos.val = s.pos.val + n.val := by
  exact cursor_advance_spec h64 (Array.Insts.CoreConvertAsRefSlice U8 N) s (arrayBuffer s.inner) rfl n (by simpa [arrayBuffer] using hn)

theorem cursor_advance_zero {T} (h64 : System.Platform.numBits = 64)
    (A : core.convert.AsRef T (Slice U8)) (s : Cursor T) (buffer : Slice U8)
    (hA : A.as_ref s.inner = .ok buffer) :
    advance A s 0#usize = .ok s := by
  obtain ⟨out,ho,hi,hp⟩ := cursor_advance_spec h64 A s buffer hA 0#usize (by simp)
  have heq : out = s := by
    cases out with
    | mk inner pos =>
      cases s with
      | mk old oldpos =>
        have hpos : pos = oldpos := by scalar_tac
        simp_all
  simpa [heq] using ho

theorem panic_advance_eq_fail (err : bytes_cursor_slice.bytes.TryGetError) :
    bytes_cursor_slice.bytes.panic_advance err = .fail .panic := by
  simp only [bytes_cursor_slice.bytes.panic_advance,core.fmt.rt.Argument.new_display_without_dictionary,core.fmt.Arguments.new]
  unfold core.fmt.rt.Argument core.fmt.Arguments
  rw [bind_ok,bind_ok,bind_ok]

theorem cursor_advance_invalid {T} (h64 : System.Platform.numBits = 64)
    (A : core.convert.AsRef T (Slice U8)) (s : Cursor T) (buffer : Slice U8)
    (hA : A.as_ref s.inner = .ok buffer) (n : Usize)
    (hn : buffer.val.length - s.pos.val < n.val) :
    advance A s n = .fail .panic := by
  obtain ⟨max_cnt, hm, hv⟩ := _root_.bytes.saturating_sub_usize_u64_spec h64 (Slice.len buffer) s.pos
  have hn' : n > max_cnt := by
    simp only [Slice.len] at hv
    scalar_tac
  unfold advance bytes_cursor_slice.core.io.cursor.Cursor.Insts.BytesBufBuf_implBuf.advance
  simp only [bytes_cursor_slice.core.io.cursor.Cursor.get_ref,bytes_cursor_slice.core.io.cursor.Cursor.position,bind_ok,hA]
  rw [sub_bridge,hm,bind_ok,ite_eq_left hn',panic_advance_eq_fail]
  simp

abbrev actualSliceAsRef : core.convert.AsRef (Slice U8) (Slice U8) :=
  bytes_cursor_slice.Shared0T.Insts.CoreConvertAsRef
    (bytes_cursor_slice.Slice.Insts.CoreConvertAsRefSlice U8)

theorem actual_slice_as_ref (s : Slice U8) :
    actualSliceAsRef.as_ref s = .ok s := rfl

theorem slice_remaining_spec (h64 : System.Platform.numBits = 64)
    (s : Cursor (Slice U8)) :
    ∃ out, bytes_cursor_slice.remaining s = .ok out ∧
      out.val = s.inner.val.length - s.pos.val := by
  exact cursor_remaining_spec h64 actualSliceAsRef s s.inner rfl

theorem slice_chunk_spec (h64 : System.Platform.numBits = 64)
    (s : Cursor (Slice U8)) :
    ∃ out, bytes_cursor_slice.chunk s = .ok out ∧
      out.val = s.inner.val.drop s.pos.val := by
  exact cursor_chunk_spec h64 actualSliceAsRef s s.inner rfl

theorem slice_advance_spec (h64 : System.Platform.numBits = 64)
    (s : Cursor (Slice U8)) (n : Usize)
    (hn : n.val ≤ s.inner.val.length - s.pos.val) :
    ∃ out, bytes_cursor_slice.advance s n = .ok out ∧
      out.inner = s.inner ∧ out.pos.val = s.pos.val + n.val := by
  exact cursor_advance_spec h64 actualSliceAsRef s s.inner rfl n hn

theorem slice_advance_zero (h64 : System.Platform.numBits = 64)
    (s : Cursor (Slice U8)) :
    bytes_cursor_slice.advance s 0#usize = .ok s :=
  cursor_advance_zero h64 actualSliceAsRef s s.inner rfl

theorem slice_advance_invalid (h64 : System.Platform.numBits = 64)
    (s : Cursor (Slice U8)) (n : Usize)
    (hn : s.inner.val.length - s.pos.val < n.val) :
    bytes_cursor_slice.advance s n = .fail .panic :=
  cursor_advance_invalid h64 actualSliceAsRef s s.inner rfl n hn

end bytes_cursor_proofs

namespace bytes_cursor_proofs
/-- Successful advancement consumes the logical suffix, including exhausted cursors. -/
theorem slice_advance_view (h64 : System.Platform.numBits = 64)
    (s : Cursor (Slice U8)) (n : Usize)
    (hn : n.val ≤ s.inner.val.length - s.pos.val) :
    ∃ out, bytes_cursor_slice.advance s n = .ok out ∧ out.inner = s.inner ∧
      out.inner.val.drop out.pos.val = (s.inner.val.drop s.pos.val).drop n.val := by
  obtain ⟨out,ho,hi,hp⟩ := slice_advance_spec h64 s n hn
  exact ⟨out,ho,hi,by simp [hi,hp,List.drop_drop,Nat.add_comm]⟩

theorem slice_advance_sequence (h64 : System.Platform.numBits = 64)
    (s : Cursor (Slice U8)) (n m : Usize)
    (hn : n.val + m.val ≤ s.inner.val.length - s.pos.val) :
    ∃ out, (do let mid ← bytes_cursor_slice.advance s n
               bytes_cursor_slice.advance mid m) = .ok out ∧
      out.inner = s.inner ∧ out.pos.val = s.pos.val + n.val + m.val ∧
      out.inner.val.drop out.pos.val =
        (s.inner.val.drop s.pos.val).drop (n.val + m.val) := by
  obtain ⟨mid,hm,hi,hp⟩ := slice_advance_spec h64 s n (by omega)
  have hnext : m.val ≤ mid.inner.val.length - mid.pos.val := by
    rw [hi,hp]
    omega
  obtain ⟨out,ho,hi',hp'⟩ := slice_advance_spec h64 mid m hnext
  refine ⟨out,?_,hi'.trans hi,?_,?_⟩
  · rw [hm]
    have hb := @bind_ok (Cursor (Slice U8)) (Cursor (Slice U8)) mid (fun x => bytes_cursor_slice.advance x m)
    exact hb.trans ho
  · omega
  · simp [hi',hi,hp',hp,List.drop_drop,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
end bytes_cursor_proofs
