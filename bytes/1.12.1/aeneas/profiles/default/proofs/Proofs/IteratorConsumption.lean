import BytesAdapters
import Proofs.AdapterConsumption
open Aeneas Aeneas.Std Result
namespace bytes_buffers
abbrev Iterator := bytes_adapters.bytes.buf.iter.IntoIter
abbrev iteratorNext := @bytes_adapters.bytes.buf.iter.IntoIter.Insts.CoreIterTraitsIteratorIteratorU8.next
abbrev iteratorSizeHint := @bytes_adapters.bytes.buf.iter.IntoIter.Insts.CoreIterTraitsIteratorIteratorU8.size_hint

/-- Actual count-pair characterization. For conceptual views exceeding usize
this alone does not establish the Iterator upper-bound contract. -/
theorem iterator_size_hint_spec {T : Type _} (B : BytesBuf T) (view : T → List U8)
    (laws : Laws B view) (s : Iterator T) :
    ∃ out, iteratorSizeHint B s = .ok out ∧ out.2 = some out.1 ∧
      out.1.val = Nat.min Usize.max (view s.inner).length := by
  obtain ⟨n,hn,hval⟩ := wp_success (laws.remaining s.inner)
  exact ⟨(n,some n),by simp [iteratorSizeHint,
    bytes_adapters.bytes.buf.iter.IntoIter.Insts.CoreIterTraitsIteratorIteratorU8.size_hint,hn],rfl,hval⟩

theorem iterator_next_empty {T : Type _} (B : BytesBuf T) (view : T → List U8)
    (laws : Laws B view) (s : Iterator T) (hempty : view s.inner = []) :
    iteratorNext B s = .ok (none,s) := by
  obtain ⟨b,hb,hval⟩ := wp_success (laws.has_remaining s.inner)
  have hf : b = false := by simpa [hempty] using hval
  simp [iteratorNext,
    bytes_adapters.bytes.buf.iter.IntoIter.Insts.CoreIterTraitsIteratorIteratorU8.next,hb,hf]

theorem iterator_next_cons {T : Type _} (B : BytesBuf T) (view : T → List U8)
    (laws : Laws B view) (s : Iterator T) (x : U8) (xs : List U8)
    (hview : view s.inner = x::xs) :
    ∃ out, iteratorNext B s = .ok (some x,out) ∧ view out.inner = xs := by
  obtain ⟨b,hb,hval⟩ := wp_success (laws.has_remaining s.inner)
  have ht : b = true := by simpa [hview] using hval
  obtain ⟨chunk,hchunk,hprefix,hempty⟩ := wp_success (laws.chunk s.inner)
  have hne : chunk.val ≠ [] := by simp_all
  have hidx : 0 < chunk.val.length := by cases h : chunk.val <;> simp_all
  obtain ⟨v,hv,hvval⟩ := wp_success (Slice.index_usize_spec chunk 0#usize (by simpa using hidx))
  have hvx : v = x := by
    obtain ⟨tail,htail⟩ := hprefix
    cases hc : chunk.val with
    | nil => simp_all
    | cons y ys =>
      have hy : y = x := by simpa [hc,hview] using congrArg List.head? htail
      simpa [hc,hy] using hvval
  obtain ⟨inner,hinner,hdrop⟩ := wp_success (laws.advance s.inner 1#usize (by simp [hview]))
  refine ⟨⟨inner⟩,?_,?_⟩
  · simp [iteratorNext,
      bytes_adapters.bytes.buf.iter.IntoIter.Insts.CoreIterTraitsIteratorIteratorU8.next,
      hb,ht,hchunk,hv,hvx,hinner]
  · simpa [hview] using hdrop
theorem iterator_next_spec {T : Type _} (B : BytesBuf T) (view : T → List U8)
    (laws : Laws B view) (s : Iterator T) :
    ∃ out, iteratorNext B s = .ok out ∧
      out.1 = (view s.inner).head? ∧ view out.2.inner = (view s.inner).drop 1 ∧
      (view s.inner = [] → out.2 = s) := by
  cases hv : view s.inner with
  | nil =>
    exact ⟨(none,s),iterator_next_empty B view laws s hv,by simp,by simp [hv],by simp⟩
  | cons x xs =>
    obtain ⟨s',hs',hview⟩ := iterator_next_cons B view laws s x xs hv
    exact ⟨(some x,s'),hs',by simp,by simpa using hview,by simp⟩

theorem iterator_exhaustion_stable {T : Type _} (B : BytesBuf T) (view : T → List U8)
    (laws : Laws B view) (s : Iterator T) (hempty : view s.inner = []) :
    (do
      let (_,s') ← iteratorNext B s
      iteratorNext B s') = .ok (none,s) := by
  simp [iterator_next_empty B view laws s hempty]

theorem iterator_size_hint_exact {T : Type _} (B : BytesBuf T) (view : T → List U8)
    (laws : Laws B view) (s : Iterator T) (hfit : (view s.inner).length ≤ Usize.max) :
    ∃ out, iteratorSizeHint B s = .ok out ∧ out.2 = some out.1 ∧
      out.1.val = (view s.inner).length := by
  obtain ⟨out,ho,hsome,hval⟩ := iterator_size_hint_spec B view laws s
  exact ⟨out,ho,hsome,by simpa only [Nat.min_eq_right hfit] using hval⟩

theorem slice_iterator_next_spec (s : Iterator (Slice U8)) :
    ∃ out, iteratorNext sliceBuf s = .ok out ∧
      out.1 = s.inner.val.head? ∧ out.2.inner.val = s.inner.val.drop 1 ∧
      (s.inner.val = [] → out.2 = s) :=
  iterator_next_spec sliceBuf (fun s => s.val) slice_laws s

theorem slice_iterator_size_hint_spec (s : Iterator (Slice U8)) :
    ∃ out, iteratorSizeHint sliceBuf s = .ok out ∧ out.2 = some out.1 ∧
      out.1.val = s.inner.val.length := by
  apply iterator_size_hint_exact sliceBuf (fun s => s.val) slice_laws s
  have hp := Slice.property s.inner
  scalar_tac

theorem slice_iterator_exhaustion_stable (s : Iterator (Slice U8))
    (hempty : s.inner.val = []) :
    (do
      let (_,s') ← iteratorNext sliceBuf s
      iteratorNext sliceBuf s') = .ok (none,s) :=
  iterator_exhaustion_stable sliceBuf (fun s => s.val) slice_laws s hempty

end bytes_buffers
