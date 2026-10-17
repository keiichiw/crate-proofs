module
public import Proofs.Loop4

@[expose] public section
open Aeneas.Std Aeneas.Std.WP
namespace adler2

def sumRemaining (it : core.slice.iter.Iter U32) : Nat :=
  ((it.slice.val.drop it.i).map UScalar.val).sum

private theorem sumRemaining_step (it : core.slice.iter.Iter U32)
    (h : it.i < it.slice.val.length) :
    sumRemaining it = it.slice.val[it.i].val +
      sumRemaining {it with i := it.i + 1} := by
  simp only [sumRemaining, List.drop_eq_getElem_cons h, List.map_cons, List.sum_cons]

private theorem iter_u32_next_some (it : core.slice.iter.Iter U32)
    (h : it.i < it.slice.val.length) :
    core.slice.iter.IteratorSliceIter.next it =
      Result.ok (some it.slice.val[it.i], {it with i := it.i + 1}) := by
  simp [core.slice.iter.IteratorSliceIter.next, h]
  rfl

private theorem iter_u32_next_none (it : core.slice.iter.Iter U32)
    (h : it.slice.val.length ≤ it.i) :
    core.slice.iter.IteratorSliceIter.next it = Result.ok (none, it) := by
  simp [core.slice.iter.IteratorSliceIter.next, h]

private def sumInv (source : Slice U32) (target limit : Nat)
    (x : core.slice.iter.Iter U32 × U32) : Prop :=
  let (it, a) := x
  it.slice = source ∧ it.i ≤ source.val.length ∧
    a.val + sumRemaining it ≤ limit ∧
    a.val + sumRemaining it = target

theorem compute_loop2_spec (it : core.slice.iter.Iter U32) (a : U32)
    (hi : it.i ≤ it.slice.val.length)
    (hbound : a.val + sumRemaining it ≤ 1506966) :
    ∃ out : U32, algo.Adler32.compute_loop2 it a = Result.ok out ∧
      out.val = a.val + sumRemaining it ∧ out.val ≤ 1506966 := by
  let target := a.val + sumRemaining it
  have hspec : WP.spec (algo.Adler32.compute_loop2 it a)
      (fun out => out.val = target ∧ out.val ≤ 1506966) := by
    unfold algo.Adler32.compute_loop2
    apply loop.spec_decr_nat
      (measure := fun (x : core.slice.iter.Iter U32 × U32) =>
        x.1.slice.val.length - x.1.i)
      (inv := sumInv it.slice target 1506966)
    · intro x hx
      rcases x with ⟨it', a'⟩
      dsimp [sumInv] at hx
      obtain ⟨hSlice, hi', hbound', htarget⟩ := hx
      have hlen : it'.slice.val.length = it.slice.val.length :=
        congrArg (fun s : Slice U32 => s.val.length) hSlice
      by_cases hnext : it'.i < it'.slice.val.length
      · have hnextEq := iter_u32_next_some it' hnext
        simp only
        unfold algo.Adler32.compute_loop2.body
        rw [hnextEq]
        simp only [bind_ok]
        change WP.spec (do
          let a1 ← a' + it'.slice.val[it'.i]
          Result.ok (ControlFlow.cont ({it' with i := it'.i + 1}, a1))) _
        have hsum := sumRemaining_step it' hnext
        have hsafety : a'.val + it'.slice.val[it'.i].val < 4294967296 := by omega
        obtain ⟨a1, ha1, hav⟩ := u32_add_ok a' it'.slice.val[it'.i] hsafety
        rw [ha1]
        simp only [bind_ok, WP.spec_ok]
        refine ⟨?_, by omega⟩
        dsimp [sumInv]
        refine ⟨hSlice, by omega, ?_, ?_⟩
        · rw [hav]
          omega
        · rw [hav]
          omega
      · have hnextEq := iter_u32_next_none it' (by omega)
        dsimp only
        unfold algo.Adler32.compute_loop2.body
        rw [hnextEq]
        simp only [bind_ok]
        change WP.spec (Result.ok (ControlFlow.done a')) _
        simp only [WP.spec_ok]
        have heq : it'.i = it'.slice.val.length := by omega
        have hzero : sumRemaining it' = 0 := by simp [sumRemaining, heq]
        constructor
        · omega
        · omega
    · exact ⟨rfl, hi, hbound, rfl⟩
  obtain ⟨out, hout, hprops⟩ := spec_result_ok hspec
  exact ⟨out, hout, hprops⟩

theorem compute_loop3_spec (it : core.slice.iter.Iter U32) (b : U32)
    (hi : it.i ≤ it.slice.val.length)
    (hbound : b.val + sumRemaining it ≤ 1506966) :
    ∃ out : U32, algo.Adler32.compute_loop3 it b = Result.ok out ∧
      out.val = b.val + sumRemaining it ∧ out.val ≤ 1506966 := by
  have heq : algo.Adler32.compute_loop3 it b =
      algo.Adler32.compute_loop2 it b := by rfl
  rw [heq]
  exact compute_loop2_spec it b hi hbound

end adler2
