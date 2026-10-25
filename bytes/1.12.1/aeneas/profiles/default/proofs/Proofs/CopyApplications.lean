import Proofs.CopyLoop
import Proofs.ChainConsumption
open Aeneas Aeneas.Std Result
namespace bytes_buffers
/-- The checked default loop instantiated with the verified actual Take methods. -/
theorem take_slice_copy_success (s : Take (Slice U8)) (dst : Slice U8)
    (h : dst.val.length ≤ (takeView (fun x => x.val) s).length) :
    ∃ out, bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default
      (takeBuf sliceBuf) s dst = .ok out ∧ out.1 = .Ok () ∧
      takeView (fun x => x.val) out.2.1 =
        (takeView (fun x => x.val) s).drop dst.val.length ∧
      out.2.2.val = (takeView (fun x => x.val) s).take dst.val.length :=
  try_copy_to_slice_success _ _ (take_laws sliceBuf _ slice_laws) s dst h

/-- Crossing the Chain boundary uses the two actual slice implementations. -/
theorem chain_slice_copy_success (s : Chain (Slice U8) (Slice U8)) (dst : Slice U8)
    (h : dst.val.length ≤ (chainView (fun x => x.val) (fun x => x.val) s).length) :
    ∃ out, bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default
      (chainBuf sliceBuf sliceBuf) s dst = .ok out ∧ out.1 = .Ok () ∧
      chainView (fun x => x.val) (fun x => x.val) out.2.1 =
        (chainView (fun x => x.val) (fun x => x.val) s).drop dst.val.length ∧
      out.2.2.val = (chainView (fun x => x.val) (fun x => x.val) s).take dst.val.length :=
  try_copy_to_slice_success _ _ (chain_laws sliceBuf sliceBuf _ _ slice_laws slice_laws) s dst h

/-- A concrete nested adapter composition, without assumed application laws. -/
theorem take_chain_slice_copy_success
    (s : Take (Chain (Slice U8) (Slice U8))) (dst : Slice U8)
    (h : dst.val.length ≤
      (takeView (chainView (fun x => x.val) (fun x => x.val)) s).length) :
    ∃ out, bytes_copy.buf.buf_impl.Buf.try_copy_to_slice.default
      (takeBuf (chainBuf sliceBuf sliceBuf)) s dst = .ok out ∧ out.1 = .Ok () ∧
      takeView (chainView (fun x => x.val) (fun x => x.val)) out.2.1 =
        (takeView (chainView (fun x => x.val) (fun x => x.val)) s).drop dst.val.length ∧
      out.2.2.val =
        (takeView (chainView (fun x => x.val) (fun x => x.val)) s).take dst.val.length :=
  try_copy_to_slice_success _ _
    (take_chain_laws sliceBuf sliceBuf _ _ slice_laws slice_laws) s dst h
end bytes_buffers
