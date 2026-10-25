import Bytes
open Aeneas Aeneas.Std Result
namespace bytes

theorem reader_new_spec {B : Type _} (inner : B) :
    ∃ out, buf.reader.new inner = .ok out ∧ out.buf = inner := by
  exact ⟨⟨inner⟩, rfl, rfl⟩

theorem reader_get_ref_spec {B : Type _} (s : buf.reader.Reader B) :
    ∃ out, buf.reader.Reader.get_ref s = .ok out ∧ out = s.buf := by
  exact ⟨s.buf, rfl, rfl⟩

theorem reader_get_mut_spec {B : Type _} (s : buf.reader.Reader B) :
    ∃ out, buf.reader.Reader.get_mut s = .ok out ∧ out.1 = s.buf ∧
      (∀ replacement, (out.2 replacement).buf = replacement) := by
  exact ⟨(s.buf, fun replacement => {buf := replacement}), rfl, rfl, fun _ => rfl⟩

theorem reader_into_inner_spec {B : Type _} (s : buf.reader.Reader B) :
    ∃ out, buf.reader.Reader.into_inner s = .ok out ∧ out = s.buf := by
  exact ⟨s.buf, rfl, rfl⟩

theorem writer_new_spec {B : Type _} (inner : B) :
    ∃ out, buf.writer.new inner = .ok out ∧ out.buf = inner := by
  exact ⟨⟨inner⟩, rfl, rfl⟩

theorem writer_get_ref_spec {B : Type _} (s : buf.writer.Writer B) :
    ∃ out, buf.writer.Writer.get_ref s = .ok out ∧ out = s.buf := by
  exact ⟨s.buf, rfl, rfl⟩

theorem writer_get_mut_spec {B : Type _} (s : buf.writer.Writer B) :
    ∃ out, buf.writer.Writer.get_mut s = .ok out ∧ out.1 = s.buf ∧
      (∀ replacement, (out.2 replacement).buf = replacement) := by
  exact ⟨(s.buf, fun replacement => {buf := replacement}), rfl, rfl, fun _ => rfl⟩

theorem writer_into_inner_spec {B : Type _} (s : buf.writer.Writer B) :
    ∃ out, buf.writer.Writer.into_inner s = .ok out ∧ out = s.buf := by
  exact ⟨s.buf, rfl, rfl⟩
end bytes
