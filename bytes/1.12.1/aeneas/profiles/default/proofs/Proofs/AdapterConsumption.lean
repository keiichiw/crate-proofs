import BytesAdapters
import Proofs.BufferLaws
import Mathlib.Data.List.Infix
open Aeneas Aeneas.Std Result
namespace bytes_buffers
abbrev Take := bytes_adapters.bytes.buf.take.Take
abbrev Chain := bytes_adapters.bytes.buf.chain.Chain
abbrev takeRemaining := @bytes_adapters.bytes.buf.take.Take.Insts.BytesBufBuf_implBuf.remaining
abbrev takeChunk := @bytes_adapters.bytes.buf.take.Take.Insts.BytesBufBuf_implBuf.chunk
abbrev takeAdvance := @bytes_adapters.bytes.buf.take.Take.Insts.BytesBufBuf_implBuf.advance
abbrev chainRemaining := @bytes_adapters.bytes.buf.chain.Chain.Insts.BytesBufBuf_implBuf.remaining
abbrev chainChunk := @bytes_adapters.bytes.buf.chain.Chain.Insts.BytesBufBuf_implBuf.chunk
abbrev chainAdvance := @bytes_adapters.bytes.buf.chain.Chain.Insts.BytesBufBuf_implBuf.advance

def takeView {T : Type _} (view : T → List U8) (s : Take T) := (view s.inner).take s.limit.val
def chainView {T U : Type _} (a : T → List U8) (b : U → List U8) (s : Chain T U) := a s.a ++ b s.b

abbrev sliceBuf := bytes_adapters.Shared0SliceU8.Insts.BytesBufBuf_implBuf

theorem slice_laws : Laws sliceBuf (fun s => s.val) := by
  constructor
  · intro s
    simp only [sliceBuf,bytes_adapters.Shared0SliceU8.Insts.BytesBufBuf_implBuf.remaining,WP.spec_ok]
    have hs := Slice.property s
    simp_all [Slice.len,Slice.length,Usize.max]
  · intro s
    simp [sliceBuf,bytes_adapters.Shared0SliceU8.Insts.BytesBufBuf_implBuf.chunk,WP.spec_ok]
  · intro s n hn
    change bytes_adapters.Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance s n ⦃ out => out.val = s.val.drop n.val ⦄
    unfold bytes_adapters.Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance
    dsimp only
    split
    · scalar_tac
    · step
      simp_all
  · intro s
    simp only [sliceBuf,bytes_adapters.Shared0SliceU8.Insts.BytesBufBuf_implBuf.has_remaining,
      bytes_adapters.Shared0SliceU8.Insts.BytesBufBuf_implBuf.remaining,bind_ok,WP.spec_ok]
    have h : (s.len > 0#usize) ↔ s.val ≠ [] := by
      simp [Slice.len, Slice.length, UScalar.lt_equiv, List.length_pos_iff_ne_nil]
    simp only [h]

theorem take_remaining_spec {T} (B : BytesBuf T) (view : T → List U8)
    (h : Laws B view) (s : Take T) :
    takeRemaining B s ⦃ out => out.val = (takeView view s).length ⦄ := by
  unfold takeRemaining bytes_adapters.bytes.buf.take.Take.Insts.BytesBufBuf_implBuf.remaining
  obtain ⟨r, hr, hv⟩ := wp_success (h.remaining s.inner)
  rw [hr, bind_ok]
  simp [core.cmp.min, core.cmp.OrdUsize, liftFun2, WP.spec_ok, takeView, List.length_take]
  rw [hv]
  have hs : s.limit.val ≤ Usize.max := by scalar_tac
  simp only [Nat.min_def] at *
  split_ifs <;> omega

theorem take_advance_spec {T} (B : BytesBuf T) (view : T → List U8)
    (h : Laws B view) (s : Take T) (n : Usize)
    (hn : n.val ≤ (takeView view s).length) :
    takeAdvance B s n ⦃ out => view out.inner = (view s.inner).drop n.val ∧
      out.limit.val = s.limit.val - n.val ∧
      takeView view out = (takeView view s).drop n.val ⦄ := by
  have hn' : n.val ≤ (view s.inner).length ∧ n.val ≤ s.limit.val := by
    have hh := hn
    simp only [takeView, List.length_take, Nat.le_min] at hh
    exact ⟨hh.2, hh.1⟩
  obtain ⟨v,hv,hvv⟩ := wp_success (h.advance s.inner n hn'.1)
  unfold takeAdvance bytes_adapters.bytes.buf.take.Take.Insts.BytesBufBuf_implBuf.advance
  step
  rw [hv, bind_ok]
  step
  simp_all [takeView, List.drop_take]

theorem take_chunk_exact {T} (B : BytesBuf T) (s : Take T) (c : Slice U8)
    (hc : B.chunk s.inner = .ok c) :
    takeChunk B s ⦃ out => out.val = c.val.take s.limit.val ⦄ := by
  unfold takeChunk bytes_adapters.bytes.buf.take.Take.Insts.BytesBufBuf_implBuf.chunk
  rw [hc, bind_ok]
  simp only [core.cmp.min, core.cmp.OrdUsize, liftFun2, bind_ok]
  step
  simp_all [List.take_take, Slice.len]
  omega

theorem concrete_take_remaining (s : Take (Slice U8)) :
    bytes_adapters.concrete_take_remaining s ⦃ out =>
      out.val = (takeView (fun x => x.val) s).length ⦄ :=
  take_remaining_spec sliceBuf (fun x => x.val) slice_laws s

theorem concrete_take_advance (s : Take (Slice U8)) (n : Usize)
    (hn : n.val ≤ (takeView (fun x => x.val) s).length) :
    bytes_adapters.concrete_take_advance s n ⦃ out =>
      out.inner.val = s.inner.val.drop n.val ∧
      out.limit.val = s.limit.val - n.val ∧
      takeView (fun x => x.val) out = (takeView (fun x => x.val) s).drop n.val ⦄ :=
  take_advance_spec sliceBuf (fun x => x.val) slice_laws s n hn

theorem concrete_take_chunk (s : Take (Slice U8)) :
    bytes_adapters.concrete_take_chunk s ⦃ out =>
      out.val = takeView (fun x => x.val) s ⦄ :=
  take_chunk_exact sliceBuf s s.inner rfl

theorem slice_remaining_spec (s : Slice U8) :
    bytes_adapters.slice_remaining s ⦃ out => out.val = s.val.length ⦄ := by
  simp [bytes_adapters.slice_remaining, bytes_adapters.Shared0SliceU8.Insts.BytesBufBuf_implBuf.remaining,
    WP.spec_ok, Slice.len]

theorem slice_chunk_spec (s : Slice U8) :
    bytes_adapters.slice_chunk s ⦃ out => out = s ⦄ := by
  simp [bytes_adapters.slice_chunk, bytes_adapters.Shared0SliceU8.Insts.BytesBufBuf_implBuf.chunk,WP.spec_ok]

theorem slice_has_remaining_spec (s : Slice U8) :
    bytes_adapters.slice_has_remaining s ⦃ out => out = decide (s.val ≠ []) ⦄ :=
  slice_laws.has_remaining s

theorem take_has_remaining_spec {T} (B : BytesBuf T) (view : T → List U8)
    (h : Laws B view) (s : Take T) :
    bytes_adapters.take_has_remaining B s ⦃ out =>
      out = decide (takeView view s ≠ []) ⦄ := by
  obtain ⟨v,hv,hvv⟩ := wp_success (take_remaining_spec B view h s)
  unfold bytes_adapters.take_has_remaining
    bytes_adapters.bytes.buf.take.Take.Insts.BytesBufBuf_implBuf.has_remaining
  change bytes_adapters.bytes.buf.take.Take.Insts.BytesBufBuf_implBuf.remaining B s = .ok v at hv
  rw [hv]
  simp only [bind_ok, WP.spec_ok]
  have hp : (v > 0#usize) ↔ takeView view s ≠ [] := by
    simp [UScalar.lt_equiv, hvv, List.length_pos_iff_ne_nil]
  simp only [hp]

theorem concrete_take_has_remaining (s : Take (Slice U8)) :
    bytes_adapters.take_has_remaining sliceBuf s ⦃ out =>
      out = decide (takeView (fun x => x.val) s ≠ []) ⦄ :=
  take_has_remaining_spec sliceBuf (fun x => x.val) slice_laws s

def takeBuf {T} (B : BytesBuf T) : BytesBuf (Take T) where
  remaining := takeRemaining B
  chunk := takeChunk B
  advance := takeAdvance B
  has_remaining := bytes_adapters.take_has_remaining B

theorem take_laws {T} (B : BytesBuf T) (view : T → List U8)
    (h : Laws B view) : Laws (takeBuf B) (takeView view) := by
  constructor
  · intro s
    obtain ⟨r,hr,hv⟩ := wp_success (take_remaining_spec B view h s)
    change takeRemaining B s ⦃ _ ⦄
    rw [hr,WP.spec_ok,hv]
    have hs : (takeView view s).length ≤ Usize.max := by
      have hb : s.limit.val ≤ Usize.max := by scalar_tac
      simp only [takeView,List.length_take]
      omega
    exact (Nat.min_eq_right hs).symm
  · intro s
    obtain ⟨c,hc,hpre,hempty⟩ := wp_success (h.chunk s.inner)
    obtain ⟨r,hr,hv⟩ := wp_success (take_chunk_exact B s c hc)
    change takeChunk B s ⦃ _ ⦄
    rw [hr,WP.spec_ok]
    simp only [hv,takeView]
    constructor
    · exact hpre.take _
    · simp only [List.take_eq_nil_iff]
      tauto
  · intro s n hn
    obtain ⟨r,hr,hv⟩ := wp_success (take_advance_spec B view h s n hn)
    change takeAdvance B s n ⦃ _ ⦄
    rw [hr,WP.spec_ok]
    exact hv.2.2
  · exact take_has_remaining_spec B view h

theorem take_advance_over_limit {T} (B : BytesBuf T) (s : Take T) (n : Usize)
    (hn : s.limit.val < n.val) :
    takeAdvance B s n = .fail .assertionFailure := by
  unfold takeAdvance bytes_adapters.bytes.buf.take.Take.Insts.BytesBufBuf_implBuf.advance
  have hh : ¬ n ≤ s.limit := by scalar_tac
  simp [massert,hh]

theorem take_advance_sequence {T} (B : BytesBuf T) (view : T → List U8)
    (h : Laws B view) (s : Take T) (n m : Usize)
    (hn : n.val + m.val ≤ (takeView view s).length) :
    (do let mid ← takeAdvance B s n; takeAdvance B mid m) ⦃ out =>
      takeView view out = (takeView view s).drop (n.val + m.val) ∧
      out.limit.val = s.limit.val - (n.val + m.val) ⦄ := by
  obtain ⟨mid,hm,hi,hl,hview⟩ := wp_success (take_advance_spec B view h s n (by omega))
  have hnext : m.val ≤ (takeView view mid).length := by
    rw [hview,List.length_drop]
    omega
  obtain ⟨out,ho,hi',hl',hview'⟩ := wp_success (take_advance_spec B view h mid m hnext)
  rw [hm,bind_ok,ho,WP.spec_ok]
  simp_all [List.drop_drop,Nat.sub_sub]

theorem take_dictionary_exact {T} (B : BytesBuf T) :
    takeBuf B = bytes_adapters.bytes.buf.take.Take.Insts.BytesBufBuf_implBuf B := rfl
end bytes_buffers




