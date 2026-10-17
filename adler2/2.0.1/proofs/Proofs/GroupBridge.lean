module
public import Proofs.LaneLoop

@[expose] public section
open Aeneas.Std
namespace adler2
private theorem list_four (l : List U8) (h : l.length = 4) :
    ∃ x0 x1 x2 x3, l = [x0,x1,x2,x3] := by
  cases l with
  | nil => simp at h
  | cons x0 l =>
    cases l with
    | nil => simp at h
    | cons x1 l =>
      cases l with
      | nil => simp at h
      | cons x2 l =>
        cases l with
        | nil => simp at h
        | cons x3 l =>
          cases l with
          | nil => exact ⟨x0, x1, x2, x3, rfl⟩
          | cons x4 l => simp at h

private theorem chunkValues_four (c : Slice U8) (h : c.val.length = 4) :
    ∃ x0 x1 x2 x3, c.val = [x0,x1,x2,x3] ∧
      chunkValues c = ![x0.val,x1.val,x2.val,x3.val] := by
  obtain ⟨x0,x1,x2,x3,hc⟩ := list_four c.val h
  refine ⟨x0,x1,x2,x3,hc,?_⟩
  funext i
  fin_cases i <;> simp [chunkValues, hc]

theorem laneInv_groups (a0 c ra rb : Nat) (A B : Lanes)
    (groups : List (Slice U8))
    (hsize : ∀ g ∈ groups, g.val.length = 4)
    (hInv : laneInv a0 c ra rb A B)
    (hra : ra < modulus) (hrb : rb < modulus) :
    let r := run (ra, rb) ((groups.map Slice.val).flatten)
    let lanes := groups.foldl (fun st g => laneStep st (chunkValues g)) (A, B)
    laneInv a0 (c + 4 * a0 * groups.length)
      r.1 r.2 lanes.1 lanes.2 := by
  induction groups generalizing c ra rb A B with
  | nil =>
      simpa [run, normalize, Nat.mod_eq_of_lt hra, Nat.mod_eq_of_lt hrb] using hInv
  | cons g gs ih =>
      have hg := hsize g (by simp)
      obtain ⟨x0,x1,x2,x3,hgval,hvalues⟩ := chunkValues_four g hg
      have htail : ∀ h ∈ gs, h.val.length = 4 := by
        intro h hh
        exact hsize h (by simp [hh])
      have hStep := laneInv_run_four a0 c ra rb A B x0 x1 x2 x3 hInv
      have hnorm := run_normalized (ra,rb) g.val
      have hIH := ih (c := c + 4*a0)
        (ra := (run (ra,rb) g.val).1) (rb := (run (ra,rb) g.val).2)
        (A := (laneStep (A,B) (chunkValues g)).1)
        (B := (laneStep (A,B) (chunkValues g)).2)
        htail (by simpa [laneStep, hvalues, hgval] using hStep)
        hnorm.1 hnorm.2
      simpa [List.map_cons, List.flatten_cons, List.foldl_cons,
        List.length_cons, run_append, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, Prod.mk.eta] using hIH

end adler2
