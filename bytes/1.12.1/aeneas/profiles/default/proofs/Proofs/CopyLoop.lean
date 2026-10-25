import Proofs.CopyConsumption
import Proofs.CopyListLemmas
open Aeneas Aeneas.Std Result
namespace bytes_buffers
/-- The original default loop terminates for every lawful chunk partition.
The destination length decreases, and the actual writeback closures preserve bytes. -/
theorem copy_loop_general {T} (B : BytesBuf T) (view : T → List U8)
    (laws : Laws B view) (s : T) (dst : Slice U8)
    (back : Slice U8 → Slice U8) (hfit : dst.val.length ≤ (view s).length) :
    bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default_loop B back s dst ⦃ out =>
      view out.1 = (view s).drop dst.val.length ∧
      ∃ filled, out.2 = back filled ∧ filled.val = (view s).take dst.val.length ⦄ := by
  generalize hn : dst.val.length = n
  induction n using Nat.strong_induction_on generalizing s dst back with
  | h n ih =>
    unfold bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default_loop
    unfold loop
    unfold bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default_loop.body
    by_cases hz : dst.val = []
    · have hn0 : n = 0 := by simpa [hz] using hn.symm
      simp only [core.slice.Slice.is_empty, Slice.length, hz, hn0, List.length_nil, decide_true, ite_true, bind_ok, WP.spec_ok, List.drop_zero, List.take_zero, true_and]
      exact ⟨dst,rfl,hz⟩
    · obtain ⟨src,ec,pc⟩ := wp_success (laws.chunk s)
      have hdz : dst.length ≠ 0 := by simpa using hz
      simp only [core.slice.Slice.is_empty, hdz, decide_false, Bool.false_eq_true,
        ↓reduceIte, bind_ok]
      unfold bytes_copy.Mut0T.Insts.BytesBufBuf_implBuf.chunk
      rw [ec,bind_ok]
      simp only [core.cmp.impls.OrdUsize.min]
      let cnt := if dst.len < src.len then dst.len else src.len
      have hcntdst : cnt.val ≤ dst.val.length := by dsimp [cnt]; split <;> scalar_tac
      have hcntsrc : cnt.val ≤ src.val.length := by dsimp [cnt]; split <;> scalar_tac
      have hpos : 0 < cnt.val := by
        have hsrc : src.val ≠ [] := by
          intro he
          have hv := pc.2.mp he
          simp [hv] at hfit
          exact hz (by simpa using hfit)
        have hp : 0 < src.val.length := by simpa only [List.length_pos_iff_ne_nil] using hsrc
        dsimp [cnt]; split <;> scalar_tac
      simp only [lift,bind_ok]
      step as ⟨x,hpart,hpartlen,hrestore⟩
      rcases x with ⟨part,restore⟩
      dsimp only at *
      step as ⟨piece,hpiece,hpiecelen⟩
      step as ⟨copied,hcopied⟩
      step as ⟨x,htailval,htaillen,hfinish⟩
      rcases x with ⟨tail,finish⟩
      dsimp only at *
      obtain ⟨next,ea,pa⟩ := wp_success (laws.advance s cnt (le_trans hcntsrc pc.1.length_le))
      change B.advance s cnt = .ok next at ea
      rw [ea]
      simp only [bind_ok]
      simp
      have hlenrestore : (restore copied).val.length = dst.val.length := by
        rw [hrestore, List.length_setSlice!]
      have htaillength : tail.val.length = dst.val.length - cnt.val := by
        simpa only [Slice.length, hlenrestore] using htaillen
      have htailfit : tail.val.length ≤ (view next).length := by
        rw [htaillength,pa,List.length_drop]
        omega
      have hsmaller : tail.val.length < n := by rw [htaillength]; omega
      have hrec := ih tail.val.length hsmaller next tail
        (fun z => back (finish z)) htailfit rfl
      unfold bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default_loop at hrec
      unfold bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default_loop.body at hrec
      simp only [bytes_copy.Mut0T.Insts.BytesBufBuf_implBuf.chunk,
        core.cmp.impls.OrdUsize.min, lift, bind_ok] at hrec
      simp at hrec
      apply WP.spec_mono hrec
      intro out hout
      rcases hout with ⟨hnext,filled,hout,hfilled⟩
      constructor
      · rw [hnext,pa,List.drop_drop,htaillength]
        congr 1
        omega
      · refine ⟨finish filled,hout,?_⟩
        rw [hfinish,hrestore,hcopied,hpiece]
        simp only [List.slice_zero_j]
        rw [hfilled,pa,htaillength]
        simpa only [hn] using copy_fragment_completion dst.val src.val (view s) cnt.val pc.1 hcntdst hcntsrc hfit

theorem try_copy_to_slice_success {T} (B : BytesBuf T) (view : T → List U8)
    (laws : Laws B view) (s : T) (dst : Slice U8)
    (hfit : dst.val.length ≤ (view s).length) :
    ∃ out, bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default B s dst = .ok out ∧
      out.1 = .Ok () ∧ view out.2.1 = (view s).drop dst.val.length ∧
      out.2.2.val = (view s).take dst.val.length := by
  obtain ⟨n,en,pn⟩ := wp_success (laws.remaining s)
  have hdmax : dst.val.length ≤ Usize.max := dst.property
  have hnval : dst.val.length ≤ n.val := by
    rw [pn]
    simp only [Nat.min_def]
    split_ifs <;> omega
  have hn : ¬ n < Slice.len dst := by scalar_tac
  obtain ⟨out,eo,ho⟩ := wp_success (copy_loop_general B view laws s dst id hfit)
  obtain ⟨hd,filled,he,hfilled⟩ := ho
  refine ⟨(.Ok (),out),?_,rfl,hd,?_⟩
  · unfold bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default
      bytes_copy.Mut0T.Insts.BytesBufBuf_implBuf.remaining
    rw [en,bind_ok,ite_eq_right hn]
    change (do let x ← bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default_loop B id s dst
               .ok (core.result.Result.Ok (),x)) = _
    simp [eo]
  · simpa only [he,id_eq] using hfilled

theorem try_copy_to_slice_total {T} (B : BytesBuf T) (view : T → List U8)
    (laws : Laws B view) (s : T) (dst : Slice U8) :
    ∃ out, bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default B s dst = .ok out ∧
      if dst.val.length ≤ (view s).length then
        out.1 = .Ok () ∧ view out.2.1 = (view s).drop dst.val.length ∧
          out.2.2.val = (view s).take dst.val.length
      else ∃ err, out = (.Err err, s, dst) ∧
        err.requested.val = dst.val.length ∧ err.available.val = (view s).length := by
  by_cases h : dst.val.length ≤ (view s).length
  · obtain ⟨out,ho,hp⟩ := try_copy_to_slice_success B view laws s dst h
    exact ⟨out,ho,by simpa only [h,ite_true] using hp⟩
  · obtain ⟨err,he,hr,ha⟩ := try_copy_to_slice_insufficient B view laws s dst (by omega)
    exact ⟨(.Err err,s,dst),he,by simp only [h,ite_false]; exact ⟨err,rfl,hr,ha⟩⟩
end bytes_buffers
#print axioms bytes_buffers.copy_loop_general
#print axioms bytes_buffers.try_copy_to_slice_success
#print axioms bytes_buffers.try_copy_to_slice_total

