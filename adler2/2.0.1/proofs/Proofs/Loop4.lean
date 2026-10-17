module
public import Proofs.LoopBridge
public import Proofs.Spec

@[expose] public section

open Aeneas.Std Aeneas.Std.WP

namespace adler2

def rawStep (s : Nat × Nat) (byte : U8) : Nat × Nat :=
  let a := s.1 + byte.val
  (a, s.2 + a)

def rawRun (s : Nat × Nat) (bytes : List U8) : Nat × Nat :=
  bytes.foldl rawStep s

theorem rawRun_drop_step (l : List U8) (i : Nat) (h : i < l.length)
    (a b : Nat) :
    rawRun (a, b) (l.drop i) =
      rawRun (a + l[i].val, b + a + l[i].val) (l.drop (i + 1)) := by
  unfold rawRun
  rw [List.drop_eq_getElem_cons h, List.foldl_cons]
  simp [rawStep, Nat.add_assoc]

theorem slice_iter_next_some (it : core.slice.iter.Iter U8)
    (h : it.i < it.slice.val.length) :
    core.slice.iter.IteratorSliceIter.next it =
      Result.ok (some it.slice.val[it.i], {it with i := it.i + 1}) := by
  simp [core.slice.iter.IteratorSliceIter.next, h]
  rfl

theorem slice_iter_next_none (it : core.slice.iter.Iter U8)
    (h : it.slice.val.length ≤ it.i) :
    core.slice.iter.IteratorSliceIter.next it =
      Result.ok (none, it) := by
  simp [core.slice.iter.IteratorSliceIter.next, h]

private def tailInv (source : Slice U8) (target : Nat × Nat)
    (x : core.slice.iter.Iter U8 × U32 × U32) : Prop :=
  let (it, a, b) := x
  it.slice = source ∧ it.i ≤ source.val.length ∧
    a.val + 255 * (source.val.length - it.i) ≤ 328380 ∧
    b.val + 328380 * (source.val.length - it.i) ≤ 2492106 ∧
    rawRun (a.val, b.val) (source.val.drop it.i) = target

theorem compute_loop4_spec (it : core.slice.iter.Iter U8) (a b : U32)
    (hi : it.i ≤ it.slice.val.length)
    (ha : a.val + 255 * (it.slice.val.length - it.i) ≤ 328380)
    (hb : b.val + 328380 * (it.slice.val.length - it.i) ≤ 2492106) :
    ∃ out : U32 × U32,
      algo.Adler32.compute_loop4 it a b = Result.ok out ∧
      (out.1.val, out.2.val) =
        rawRun (a.val, b.val) (it.slice.val.drop it.i) ∧
      out.1.val ≤ 328380 ∧ out.2.val ≤ 2492106 := by
  let target := rawRun (a.val, b.val) (it.slice.val.drop it.i)
  have hspec : WP.spec (algo.Adler32.compute_loop4 it a b)
      (fun out => (out.1.val, out.2.val) = target ∧
        out.1.val ≤ 328380 ∧ out.2.val ≤ 2492106) := by
    unfold algo.Adler32.compute_loop4
    apply loop.spec_decr_nat
      (measure := fun (x : core.slice.iter.Iter U8 × U32 × U32) =>
        x.1.slice.val.length - x.1.i)
      (inv := tailInv it.slice target)
    · intro x hx
      rcases x with ⟨it', a', b'⟩
      dsimp [tailInv] at hx
      obtain ⟨hSlice, hi', ha', hb', hraw⟩ := hx
      have hlen : it'.slice.val.length = it.slice.val.length :=
        congrArg (fun s : Slice U8 => s.val.length) hSlice
      by_cases hnext : it'.i < it'.slice.val.length
      · have hnextEq := slice_iter_next_some it' hnext
        simp only
        unfold algo.Adler32.compute_loop4.body
        rw [hnextEq]
        simp only [bind_ok, lift]
        change WP.spec (do
          let a1 ← a' + core.convert.num.FromU32U8.from it'.slice.val[it'.i]
          let b1 ← b' + a1
          Result.ok (ControlFlow.cont ({it' with i := it'.i + 1}, a1, b1))) _
        let byte := it'.slice.val[it'.i]
        have hbyte : byte.val ≤ 255 := by
          have h := U8.lt_succ_max byte
          omega
        have haSafety : a'.val + (core.convert.num.FromU32U8.from byte).val < 4294967296 := by
          rw [core.convert.num.FromU32U8.from_val_eq]
          omega
        obtain ⟨a1, ha1, hav⟩ := u32_add_ok a' (core.convert.num.FromU32U8.from byte) haSafety
        have ha1Bound : a1.val ≤ 328380 := by
          rw [hav, core.convert.num.FromU32U8.from_val_eq]
          omega
        have hbSafety : b'.val + a1.val < 4294967296 := by omega
        obtain ⟨b1, hb1, hbv⟩ := u32_add_ok b' a1 hbSafety
        rw [ha1]
        simp only [bind_ok]
        rw [hb1]
        simp only [bind_ok, WP.spec_ok]
        have haNew : a1.val + 255 * (it.slice.val.length - (it'.i + 1)) ≤ 328380 := by
          rw [hav, core.convert.num.FromU32U8.from_val_eq]
          omega
        have hbNew : b1.val + 328380 * (it.slice.val.length - (it'.i + 1)) ≤ 2492106 := by
          rw [hbv]
          omega
        have hstep := rawRun_drop_step it'.slice.val it'.i hnext a'.val b'.val
        simp only [hSlice] at hstep
        have hbyteEq : byte = it.slice.val[it'.i] := by
          simp [byte, hSlice]
        have hnum : a1.val = a'.val + byte.val := by
          simpa [core.convert.num.FromU32U8.from_val_eq] using hav
        have hbnum : b1.val = b'.val + a'.val + byte.val := by
          rw [hbv, hnum]
          omega
        have hrawNew : rawRun (a1.val, b1.val) (it.slice.val.drop (it'.i + 1)) = target := by
          calc
            _ = rawRun (a'.val + byte.val, b'.val + a'.val + byte.val)
                  (it.slice.val.drop (it'.i + 1)) := by
                    rw [hnum, hbnum]
            _ = rawRun (a'.val, b'.val) (it.slice.val.drop it'.i) := by
                  simpa [hbyteEq] using hstep.symm
            _ = target := hraw
        refine ⟨?_, by omega⟩
        dsimp [tailInv]
        exact ⟨hSlice, by omega, haNew, hbNew, hrawNew⟩
      · have hnextEq := slice_iter_next_none it' (by omega)
        dsimp only
        unfold algo.Adler32.compute_loop4.body
        rw [hnextEq]
        simp only [bind_ok]
        change WP.spec (Result.ok (ControlFlow.done (a', b'))) _
        simp only [WP.spec_ok]
        have heq : it'.i = it.slice.val.length := by
          rw [hSlice] at hnext
          omega
        have hraw' : (a'.val, b'.val) = target := by
          simpa [heq, rawRun] using hraw
        exact ⟨hraw', by omega, by omega⟩
    · exact ⟨rfl, hi, ha, hb, rfl⟩
  obtain ⟨out, hout, hprops⟩ := spec_result_ok hspec
  exact ⟨out, hout, hprops⟩

end adler2
