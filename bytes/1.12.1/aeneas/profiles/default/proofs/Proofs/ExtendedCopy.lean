import BytesStage3Types
import BytesExtendedCopy
import Proofs.CopyLoop
import Proofs.ChainConsumption
open Aeneas Aeneas.Std Result
namespace bytes_extended
/-- The old checked-body error and the registered error have exactly the same fields. -/
def toError (e : bytes_copy.TryGetError) : BytesTryGetError :=
  ⟨e.requested,e.available⟩
def fromError (e : BytesTryGetError) : bytes_copy.TryGetError :=
  ⟨e.requested,e.available⟩
theorem error_roundtrip_old (e : bytes_copy.TryGetError) : fromError (toError e) = e := by cases e; rfl
theorem error_roundtrip_new (e : BytesTryGetError) : toError (fromError e) = e := by cases e; rfl
theorem error_fields (e : bytes_copy.TryGetError) :
    (toError e).requested = e.requested ∧ (toError e).available = e.available := ⟨rfl,rfl⟩
theorem error_constructor (requested available : Usize) :
    toError ⟨requested,available⟩ = ⟨requested,available⟩ := rfl
theorem error_injective : Function.Injective toError := by
  intro x y h
  have := congrArg fromError h
  simpa only [error_roundtrip_old] using this

def projectBuf {T} (B : BytesBufExtended T) : BytesBuf T :=
  ⟨B.remaining,B.chunk,B.advance,B.has_remaining⟩
def mapOutcome (out : core.result.Result Unit bytes_copy.TryGetError) :
    core.result.Result Unit BytesTryGetError :=
  match out with
  | .Ok x => .Ok x
  | .Err e => .Err (toError e)
def liftChecked {T} (f : T → Slice U8 → Result (core.result.Result Unit bytes_copy.TryGetError × T × Slice U8))
    (s : T) (dst : Slice U8) : Result (core.result.Result Unit BytesTryGetError × T × Slice U8) := do
  let (result,next,written) ← f s dst
  .ok (mapOutcome result,next,written)

theorem loop_body_projection {T} (B : BytesBufExtended T)
    (back : Slice U8 → Slice U8) (s : T) (dst : Slice U8) :
    bytes_extended_copy.buf.buf_impl.Buf.try_copy_to_slice.default_loop.body B back s dst =
      bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default_loop.body (projectBuf B) back s dst := rfl

theorem loop_projection {T} (B : BytesBufExtended T)
    (back : Slice U8 → Slice U8) (s : T) (dst : Slice U8) :
    bytes_extended_copy.buf.buf_impl.Buf.try_copy_to_slice.default_loop B back s dst =
      bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default_loop (projectBuf B) back s dst := rfl

theorem checked_projection {T} (B : BytesBufExtended T) (s : T) (dst : Slice U8) :
    bytes_extended_copy.buf.buf_impl.Buf.try_copy_to_slice.default B s dst =
      liftChecked (bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default (projectBuf B)) s dst := by
  unfold bytes_extended_copy.buf.buf_impl.Buf.try_copy_to_slice.default
    bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default liftChecked
    bytes_extended_copy.Mut0T.Insts.BytesBufBuf_implBuf.remaining
    bytes_copy.Mut0T.Insts.BytesBufBuf_implBuf.remaining
  simp only [projectBuf, Std.bind_assoc]
  congr 1
  funext n
  split
  · simp [mapOutcome,toError]
  · rw [loop_projection]
    simp only [Std.bind_assoc]
    congr 1
    funext out
    rcases out with ⟨next,filled⟩
    simp [mapOutcome]

/-- Extend a concrete extracted base dictionary with its actual checked default body. -/
def extendBuf {T} (B : BytesBuf T) : BytesBufExtended T :=
  ⟨B.remaining,B.chunk,B.advance,B.has_remaining,
    liftChecked (bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default B)⟩
theorem project_extend {T} (B : BytesBuf T) : projectBuf (extendBuf B) = B := by cases B; rfl

theorem extended_checked_exact {T} (B : BytesBuf T) (s : T) (dst : Slice U8) :
    bytes_extended_copy.buf.buf_impl.Buf.try_copy_to_slice.default (extendBuf B) s dst =
      (extendBuf B).try_copy_to_slice s dst := by
  rw [checked_projection,project_extend]
  rfl

theorem default_checked_success {T} (B : BytesBufExtended T) (view : T → List U8)
    (laws : bytes_buffers.Laws (projectBuf B) view) (s : T) (dst : Slice U8)
    (h : dst.val.length ≤ (view s).length) :
    ∃ next filled,
      bytes_extended_copy.buf.buf_impl.Buf.try_copy_to_slice.default B s dst =
        .ok (.Ok (),next,filled) ∧
      view next = (view s).drop dst.val.length ∧ filled.val = (view s).take dst.val.length := by
  obtain ⟨out,eo,ho,hs,hd⟩ := bytes_buffers.try_copy_to_slice_success (projectBuf B) view laws s dst h
  rcases out with ⟨result,next,filled⟩
  dsimp only at *
  refine ⟨next,filled,?_,hs,hd⟩
  rw [checked_projection]
  unfold liftChecked
  rw [eo]
  simp [ho,mapOutcome]

theorem default_checked_insufficient {T} (B : BytesBufExtended T) (view : T → List U8)
    (laws : bytes_buffers.Laws (projectBuf B) view) (s : T) (dst : Slice U8)
    (h : (view s).length < dst.val.length) :
    ∃ err, bytes_extended_copy.buf.buf_impl.Buf.try_copy_to_slice.default B s dst =
        .ok (.Err err,s,dst) ∧
      err.requested.val = dst.val.length ∧ err.available.val = (view s).length := by
  obtain ⟨err,eo,hr,ha⟩ := bytes_buffers.try_copy_to_slice_insufficient (projectBuf B) view laws s dst h
  refine ⟨toError err,?_,hr,ha⟩
  rw [checked_projection]
  unfold liftChecked
  rw [eo]
  simp [mapOutcome]

theorem default_checked_total {T} (B : BytesBufExtended T) (view : T → List U8)
    (laws : bytes_buffers.Laws (projectBuf B) view) (s : T) (dst : Slice U8) :
    ∃ out, bytes_extended_copy.buf.buf_impl.Buf.try_copy_to_slice.default B s dst = .ok out ∧
      if dst.val.length ≤ (view s).length then
        out.1 = .Ok () ∧ view out.2.1 = (view s).drop dst.val.length ∧
          out.2.2.val = (view s).take dst.val.length
      else ∃ err, out = (.Err err,s,dst) ∧
        err.requested.val = dst.val.length ∧ err.available.val = (view s).length := by
  by_cases h : dst.val.length ≤ (view s).length
  · obtain ⟨next,filled,eo,hs,hd⟩ := default_checked_success B view laws s dst h
    exact ⟨(.Ok (),next,filled),eo,by simp only [h,ite_true]; exact ⟨True.intro,hs,hd⟩⟩
  · obtain ⟨err,eo,hr,ha⟩ := default_checked_insufficient B view laws s dst (by omega)
    exact ⟨(.Err err,s,dst),eo,by simp only [h,ite_false]; exact ⟨err,rfl,hr,ha⟩⟩

/-- Explicit checked-copy obligations; operational behavior is proved separately. -/
structure CheckedLaws {T} (B : BytesBufExtended T) (view : T → List U8) : Prop where
  success : ∀ s dst, dst.val.length ≤ (view s).length →
    ∃ next filled, B.try_copy_to_slice s dst = .ok (.Ok (),next,filled) ∧
      view next = (view s).drop dst.val.length ∧ filled.val = (view s).take dst.val.length
  shortage : ∀ s dst, (view s).length < dst.val.length →
    ∃ err, B.try_copy_to_slice s dst = .ok (.Err err,s,dst) ∧
      err.requested.val = dst.val.length ∧ err.available.val = (view s).length

theorem extend_checked_laws {T} (B : BytesBuf T) (view : T → List U8)
    (laws : bytes_buffers.Laws B view) : CheckedLaws (extendBuf B) view := by
  constructor
  · intro s dst h
    obtain ⟨out,eo,ho,hs,hd⟩ := bytes_buffers.try_copy_to_slice_success B view laws s dst h
    rcases out with ⟨result,next,filled⟩
    dsimp only at *
    refine ⟨next,filled,?_,hs,hd⟩
    rw [← extended_checked_exact,checked_projection,project_extend]
    unfold liftChecked
    rw [eo]
    simp [ho,mapOutcome]
  · intro s dst h
    obtain ⟨err,eo,hr,ha⟩ := bytes_buffers.try_copy_to_slice_insufficient B view laws s dst h
    refine ⟨toError err,?_,hr,ha⟩
    rw [← extended_checked_exact,checked_projection,project_extend]
    unfold liftChecked
    rw [eo]
    simp [mapOutcome]

theorem slice_checked_laws : CheckedLaws (extendBuf bytes_buffers.sliceBuf) (fun s => s.val) :=
  extend_checked_laws _ _ bytes_buffers.slice_laws

theorem take_checked_laws {T} (B : BytesBuf T) (view : T → List U8)
    (laws : bytes_buffers.Laws B view) :
    CheckedLaws (extendBuf (bytes_buffers.takeBuf B)) (bytes_buffers.takeView view) :=
  extend_checked_laws _ _ (bytes_buffers.take_laws B view laws)

theorem chain_checked_laws {T U} (A : BytesBuf T) (B : BytesBuf U)
    (va : T → List U8) (vb : U → List U8)
    (ha : bytes_buffers.Laws A va) (hb : bytes_buffers.Laws B vb) :
    CheckedLaws (extendBuf (bytes_buffers.chainBuf A B)) (bytes_buffers.chainView va vb) :=
  extend_checked_laws _ _ (bytes_buffers.chain_laws A B va vb ha hb)

end bytes_extended
