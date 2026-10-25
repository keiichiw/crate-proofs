import Bytes
open Aeneas Aeneas.Std Result
namespace bytes

theorem buf_take_constructor_spec {T : Type _} (inner : T) (limit : Usize) :
    ∃ out, buf.buf_impl.Buf.take.default inner limit = .ok out ∧
      out.inner = inner ∧ out.limit = limit := by
  exact ⟨⟨inner, limit⟩, rfl, rfl, rfl⟩

theorem buf_chain_constructor_spec {T U : Type _} (first : T) (second : U) :
    ∃ out, buf.buf_impl.Buf.chain.default first second = .ok out ∧
      out.a = first ∧ out.b = second := by
  exact ⟨⟨first, second⟩, rfl, rfl, rfl⟩

theorem buf_reader_constructor_spec {T : Type _} (inner : T) :
    ∃ out, buf.buf_impl.Buf.reader.default inner = .ok out ∧ out.buf = inner := by
  exact ⟨⟨inner⟩, rfl, rfl⟩

theorem bufmut_limit_constructor_spec {T : Type _} (inner : T) (limit : Usize) :
    ∃ out, buf.buf_mut.BufMut.limit.default inner limit = .ok out ∧
      out.inner = inner ∧ out.limit = limit := by
  exact ⟨⟨inner, limit⟩, rfl, rfl, rfl⟩

theorem bufmut_writer_constructor_spec {T : Type _} (inner : T) :
    ∃ out, buf.buf_mut.BufMut.writer.default inner = .ok out ∧ out.buf = inner := by
  exact ⟨⟨inner⟩, rfl, rfl⟩

theorem bufmut_chain_mut_constructor_spec {T U : Type _} (first : T) (second : U) :
    ∃ out, buf.buf_mut.BufMut.chain_mut.default first second = .ok out ∧
      out.a = first ∧ out.b = second := by
  exact ⟨⟨first, second⟩, rfl, rfl, rfl⟩

theorem chain_into_iter_constructor_spec {T U : Type _}
    (firstBuf : BytesBuf T) (secondBuf : BytesBuf U) (s : buf.chain.Chain T U) :
    ∃ out,
      buf.chain.Chain.Insts.CoreIterTraitsCollectIntoIteratorU8IntoIterChain.into_iter
        firstBuf secondBuf s = .ok out ∧ out.inner.a = s.a ∧ out.inner.b = s.b := by
  exact ⟨⟨s⟩, rfl, rfl, rfl⟩
end bytes
