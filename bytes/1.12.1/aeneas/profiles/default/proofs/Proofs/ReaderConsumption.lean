import BytesReader
import Proofs.AdapterConsumption
open Aeneas Aeneas.Std Result
namespace bytes_buffers
abbrev Reader := bytes_reader.buf.reader.Reader
abbrev readerConsume := @bytes_reader.buf.reader.Reader.Insts.AllocIoBuf_readBufRead.consume

theorem reader_consume_spec {T : Type _} (B : BytesBuf T) (view : T → List U8)
    (h : Laws B view) (s : Reader T) (n : Usize)
    (hn : n.val ≤ (view s.buf).length) :
    readerConsume B s n ⦃ out => view out.buf = (view s.buf).drop n.val ⦄ := by
  obtain ⟨inner, ei, pi⟩ := wp_success (h.advance s.buf n hn)
  unfold readerConsume bytes_reader.buf.reader.Reader.Insts.AllocIoBuf_readBufRead.consume
  rw [ei, bind_ok, WP.spec_ok]
  exact pi

theorem concrete_reader_consume (s : Reader (Slice U8)) (n : Usize)
    (hn : n.val ≤ s.buf.val.length) :
    readerConsume sliceBuf s n ⦃ out => out.buf.val = s.buf.val.drop n.val ⦄ :=
  reader_consume_spec sliceBuf (fun x => x.val) slice_laws s n hn
end bytes_buffers
