import BytesCopy
import Proofs.AdapterConsumption
open Aeneas Aeneas.Std Result
namespace bytes_buffers

theorem try_copy_to_slice_insufficient {T} (B : BytesBuf T) (view : T → List U8)
    (laws : Laws B view) (s : T) (dst : Slice U8)
    (h : (view s).length < dst.val.length) :
    ∃ err : bytes_copy.TryGetError,
      bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default B s dst =
        .ok (.Err err, s, dst) ∧
      err.requested.val = dst.val.length ∧ err.available.val = (view s).length := by
  obtain ⟨n,en,pn⟩ := wp_success (laws.remaining s)
  have hdmax : dst.val.length ≤ Usize.max := by
    have := dst.property
    exact this
  have hn : n.val = (view s).length := by
    rw [pn]; simp only [Nat.min_def]; split_ifs <;> omega
  have hlt : n < Slice.len dst := by scalar_tac
  unfold bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default
    bytes_copy.Mut0T.Insts.BytesBufBuf_implBuf.remaining
  rw [en,bind_ok,ite_eq_left hlt]
  exact ⟨_,rfl,rfl,hn⟩

theorem try_copy_to_slice_empty {T} (B : BytesBuf T) (view : T → List U8)
    (laws : Laws B view) (s : T) (dst : Slice U8) (h : dst.val = []) :
    bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default B s dst =
      .ok (.Ok (), s, dst) := by
  obtain ⟨n,en,pn⟩ := wp_success (laws.remaining s)
  unfold bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default
    bytes_copy.Mut0T.Insts.BytesBufBuf_implBuf.remaining
  rw [en,bind_ok]
  have hn : ¬ n < Slice.len dst := by scalar_tac
  rw [ite_eq_right hn]
  unfold bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default_loop
  unfold loop
  unfold bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default_loop.body
  simp [core.slice.Slice.is_empty, Slice.len, Slice.length, h]

theorem try_copy_to_slice_one_chunk {T} (B : BytesBuf T) (view : T → List U8)
    (laws : Laws B view) (s : T) (dst src : Slice U8)
    (hc : B.chunk s = .ok src) (hfit : dst.val.length ≤ src.val.length) :
    bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default B s dst ⦃ out =>
      out.1 = .Ok () ∧ view out.2.1 = (view s).drop dst.val.length ∧
      out.2.2.val = (view s).take dst.val.length ⦄ := by
  obtain ⟨n,en,pn⟩ := wp_success (laws.remaining s)
  obtain ⟨c,ec,pc⟩ := wp_success (laws.chunk s)
  have he : c = src := by rw [hc] at ec; exact (Result.ok_injective ec).symm
  subst c
  have hbound : dst.val.length ≤ (view s).length := le_trans hfit pc.1.length_le
  have hdmax : dst.val.length ≤ Usize.max := dst.property
  have hnval : dst.val.length ≤ n.val := by
    rw [pn]
    simp only [Nat.min_def]
    split_ifs <;> omega
  have hn : ¬ n < Slice.len dst := by scalar_tac
  unfold bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default
    bytes_copy.Mut0T.Insts.BytesBufBuf_implBuf.remaining
  rw [en,bind_ok,ite_eq_right hn]
  unfold bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default_loop
  unfold loop
  unfold bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default_loop.body
  step
  split
  · simp_all [WP.spec_ok]
  · unfold bytes_copy.Mut0T.Insts.BytesBufBuf_implBuf.chunk
    rw [hc,bind_ok]
    simp only [core.cmp.impls.OrdUsize.min]
    have hmin : (if dst.len < src.len then dst.len else src.len) = dst.len := by
      split
      · rfl
      · have hh : src.len = dst.len := by scalar_tac
        exact hh
    rw [hmin]
    simp only [lift,bind_ok]
    step as ⟨x,hpart,hpartlen,hrestore⟩
    rcases x with ⟨part,restore⟩
    dsimp only at *
    step as ⟨piece,hpiece,hpiecelen⟩
    step as ⟨copied,hcopied⟩
    step as ⟨x,htailval,htaillen,hfinish⟩
    rcases x with ⟨tail,finish⟩
    dsimp only at *
    obtain ⟨next,ea,pa⟩ := wp_success (laws.advance s dst.len (by scalar_tac))
    rw [ea]
    simp only [bind_ok]
    have hdlen : dst.len.val = dst.val.length := by scalar_tac
    have htail : tail.val = [] := by
      have hr := hrestore copied
      have hl : (restore copied).val.length = dst.val.length := by
        rw [hr,List.length_setSlice!]
      have ht : tail.length = 0 := by
        simpa only [Slice.length, hl, hdlen, Nat.sub_self] using htaillen
      simpa using ht
    unfold loop
    simp only [core.slice.Slice.is_empty, Slice.length, bind_ok]
    simp_all [WP.spec_ok, List.setSlice!, Slice.len]
    rcases pc.1 with ⟨rest,hrest⟩
    rw [← hrest]
    simp [List.take_take, List.take_append_of_le_length hfit]

theorem slice_try_copy_to_slice_success (s dst : Slice U8)
    (h : dst.val.length ≤ s.val.length) :
    ∃ out, bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default sliceBuf s dst = .ok out ∧
      out.1 = .Ok () ∧ out.2.1.val = s.val.drop dst.val.length ∧
      out.2.2.val = s.val.take dst.val.length := by
  exact wp_success (try_copy_to_slice_one_chunk sliceBuf (fun x => x.val)
    slice_laws s dst s rfl h)

theorem slice_try_copy_to_slice_total (s dst : Slice U8) :
    ∃ out, bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default sliceBuf s dst = .ok out ∧
      if dst.val.length ≤ s.val.length then
        out.1 = .Ok () ∧ out.2.1.val = s.val.drop dst.val.length ∧
          out.2.2.val = s.val.take dst.val.length
      else ∃ err, out = (.Err err, s, dst) ∧
        err.requested.val = dst.val.length ∧ err.available.val = s.val.length := by
  by_cases h : dst.val.length ≤ s.val.length
  · obtain ⟨out,ho,hp⟩ := slice_try_copy_to_slice_success s dst h
    exact ⟨out,ho,by simpa only [h,ite_true] using hp⟩
  · obtain ⟨err,he,hr,ha⟩ := try_copy_to_slice_insufficient sliceBuf
      (fun x => x.val) slice_laws s dst (by omega)
    exact ⟨(.Err err,s,dst),he,by simp only [h,ite_false]; exact ⟨err,rfl,hr,ha⟩⟩

end bytes_buffers
#print axioms bytes_buffers.try_copy_to_slice_insufficient
#print axioms bytes_buffers.try_copy_to_slice_empty
#print axioms bytes_buffers.try_copy_to_slice_one_chunk
#print axioms bytes_buffers.slice_try_copy_to_slice_success
#print axioms bytes_buffers.slice_try_copy_to_slice_total

