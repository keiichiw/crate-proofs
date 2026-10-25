import Aeneas
open Aeneas Aeneas.Std Result
namespace bytes_buffers
/-- Explicit assumptions for a projected interface. Concrete instances must
prove these; the record introduces no global assumption about any Rust API. -/
structure Laws {T : Type _} (B : BytesBuf T) (view : T → List U8) : Prop where
  remaining : ∀ s, B.remaining s ⦃ out => out.val = Nat.min Usize.max (view s).length ⦄
  chunk : ∀ s, B.chunk s ⦃ out => out.val.IsPrefix (view s) ∧
    (out.val = [] ↔ view s = []) ⦄
  advance : ∀ s n, n.val ≤ (view s).length →
    B.advance s n ⦃ out => view out = (view s).drop n.val ⦄
  has_remaining : ∀ s, B.has_remaining s ⦃ out => out = decide (view s ≠ []) ⦄

theorem wp_success {α : Type _} {m : Result α} {p : α → Prop}
    (h : WP.spec m p) : ∃ out, m = .ok out ∧ p out := by
  cases m using Result.cases with
  | ret x => exact ⟨x, rfl, (WP.spec_ok x).mp h⟩
  | vis effect k => exact False.elim ((WP.spec_vis effect k).mp h)
  | div => exact False.elim (WP.spec_div.mp h)
end bytes_buffers
