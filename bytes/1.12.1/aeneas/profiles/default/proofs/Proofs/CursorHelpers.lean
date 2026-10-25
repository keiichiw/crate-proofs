import Bytes
open Aeneas Aeneas.Std Result
namespace bytes
private theorem wp_to_success {α : Type _} {m : Result α} {p : α → Prop}
    (h : WP.spec m p) : ∃ out, m = .ok out ∧ p out := by
  cases m using Result.cases with
  | ret x => exact ⟨x, rfl, (WP.spec_ok x).mp h⟩
  | vis effect k => exact False.elim ((WP.spec_vis effect k).mp h)
  | div => exact False.elim (WP.spec_div.mp h)

private theorem cast_u64_val (h64 : System.Platform.numBits = 64) (x : U64) :
    lift (UScalar.cast .Usize x) ⦃ out => out.val = x.val ⦄ := by
  apply UScalar.cast_inBounds_spec
  have hx := x.hBounds
  simp only [UScalar.max, UScalarTy.numBits, h64] at ⊢
  simp only [UScalarTy.numBits] at hx
  omega

theorem min_u64_usize_spec (h64 : System.Platform.numBits = 64) (a : U64) (b : Usize) :
    ∃ out, min_u64_usize a b = .ok out ∧ out.val = Nat.min a.val b.val := by
  apply wp_to_success
  unfold min_u64_usize Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from
  have hc := cast_u64_val h64 a
  step
  simp_all

theorem saturating_sub_usize_u64_spec (h64 : System.Platform.numBits = 64) (a : Usize) (b : U64) :
    ∃ out, saturating_sub_usize_u64 a b = .ok out ∧ out.val = a.val - b.val := by
  apply wp_to_success
  unfold saturating_sub_usize_u64 Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from
  have hc := cast_u64_val h64 b
  step
  simp only [core.num.Usize.saturating_sub, UScalar.saturating_sub, UScalar.val,
    BitVec.toNat_ofNat, Nat.zero_max]
  have ha := a.hBounds
  have hab : a.val - r.val < 2 ^ UScalarTy.Usize.numBits := by omega
  simp only [UScalar.val] at hab r_post
  rw [Nat.mod_eq_of_lt hab, r_post]
end bytes
