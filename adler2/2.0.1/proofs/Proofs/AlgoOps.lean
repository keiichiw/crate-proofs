module
public import Adler2

public section

open Aeneas Aeneas.Std

namespace adler2

theorem u32x4_rem_assign_spec (self : algo.U32X4) (q : U32)
    (hq : q.val ≠ 0) :
    algo.U32X4.Insts.CoreOpsArithRemAssignU32.rem_assign self q
      ⦃ out => ∀ i : Fin 4,
        out.val[i.val].val = self.val[i.val].val % q.val ⦄ := by
  unfold algo.U32X4.Insts.CoreOpsArithRemAssignU32.rem_assign
  step*
  intro idx
  fin_cases idx <;> simp_all

theorem u32x4_add_assign_spec (self other : algo.U32X4)
    (hbound : ∀ i : Fin 4,
      self.val[i.val].val + other.val[i.val].val ≤ U32.max) :
    algo.U32X4.Insts.CoreOpsArithAddAssignU32X4.add_assign self other
      ⦃ out => ∀ i : Fin 4,
        out.val[i.val].val = self.val[i.val].val + other.val[i.val].val ⦄ := by
  have h0 := hbound ⟨0, by decide⟩
  have h1 := hbound ⟨1, by decide⟩
  have h2 := hbound ⟨2, by decide⟩
  have h3 := hbound ⟨3, by decide⟩
  unfold algo.U32X4.Insts.CoreOpsArithAddAssignU32X4.add_assign
  step* <;> simp_all
  intro idx
  fin_cases idx <;> simp_all

theorem u32x4_mul_assign_spec (self : algo.U32X4) (rhs : U32)
    (hbound : ∀ i : Fin 4,
      self.val[i.val].val * rhs.val ≤ U32.max) :
    algo.U32X4.Insts.CoreOpsArithMulAssignU32.mul_assign self rhs
      ⦃ out => ∀ i : Fin 4,
        out.val[i.val].val = self.val[i.val].val * rhs.val ⦄ := by
  have h0 := hbound ⟨0, by decide⟩
  have h1 := hbound ⟨1, by decide⟩
  have h2 := hbound ⟨2, by decide⟩
  have h3 := hbound ⟨3, by decide⟩
  unfold algo.U32X4.Insts.CoreOpsArithMulAssignU32.mul_assign
  step* <;> simp_all
  intro idx
  fin_cases idx <;> simp_all

end adler2
