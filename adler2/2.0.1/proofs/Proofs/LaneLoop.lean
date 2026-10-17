module
public import Proofs.AlgoOps
public import Proofs.AlgoHelpers
public import Proofs.LaneMath
public import Proofs.ChunkLemmas

@[expose] public section

open Aeneas Aeneas.Std

namespace adler2

def laneValues (a : algo.U32X4) : Lanes :=
  fun i => a.val[i.val].val

def chunkValues (c : Slice U8) : Lanes :=
  fun i => (c.val.map (fun x => x.val))[i.val]!

theorem u32x4_from_lanes (bytes : Slice U8) (h : 4 ≤ bytes.val.length) :
    ∃ out : algo.U32X4,
      algo.U32X4.from bytes = .ok out ∧
      laneValues out = chunkValues bytes := by
  obtain ⟨out, hout, hmap⟩ := u32x4_from_spec bytes h
  refine ⟨out, hout, ?_⟩
  funext i
  have hib : i.val < bytes.val.length := by have := i.isLt; omega
  have hi := congrArg (fun xs : List Nat => xs[i.val]!) hmap
  fin_cases i <;> simpa [laneValues, chunkValues, List.getElem!_map_eq,
    List.getElem!_take_of_lt, List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem hib, h] using hi

def aBound (k : Nat) : Nat := 65520 + 255 * k

def bBound2 (k : Nat) : Nat :=
  131040 + 131040 * k + 255 * k * (k + 1)

theorem bBound2_succ (k : Nat) :
    bBound2 (k + 1) = bBound2 k + 2 * aBound (k + 1) := by
  simp only [bBound2, aBound]
  ring

theorem aBound_le_max (k : Nat) (hk : k ≤ 5552) :
    aBound k ≤ U32.max := by
  have hmax := U32.max_eq
  simp only [aBound, hmax]
  omega

theorem bBound2_le_max (k : Nat) (hk : k ≤ 5552) :
    bBound2 k ≤ 2 * U32.max := by
  have hk1 : k + 1 ≤ 5553 := by omega
  have hm : k * (k + 1) ≤ 5552 * 5553 := Nat.mul_le_mul hk hk1
  have hmax := U32.max_eq
  simp only [bBound2, hmax]
  rw [mul_assoc 255 k (k + 1)]
  omega

theorem laneBounds_step (k a b x : Nat) (hk : k < 5552)
    (ha : a ≤ aBound k) (hb : 2 * b ≤ bBound2 k)
    (hx : x ≤ 255) :
    a + x ≤ U32.max ∧ b + (a + x) ≤ U32.max ∧
    a + x ≤ aBound (k + 1) ∧
    2 * (b + (a + x)) ≤ bBound2 (k + 1) := by
  have hnextA : a + x ≤ aBound (k + 1) := by
    simp only [aBound] at ha ⊢
    omega
  have hnextB : 2 * (b + (a + x)) ≤ bBound2 (k + 1) := by
    rw [bBound2_succ]
    omega
  have hnext : k + 1 ≤ 5552 := by omega
  have hAmax := aBound_le_max (k + 1) hnext
  have hBmax := bBound2_le_max (k + 1) hnext
  exact ⟨by omega, by omega, hnextA, hnextB⟩

theorem u32x4_from_lanes_wp (bytes : Slice U8)
    (h : 4 ≤ bytes.val.length) :
    algo.U32X4.from bytes ⦃ out => laneValues out = chunkValues bytes ⦄ := by
  obtain ⟨out, hout, hval⟩ := u32x4_from_lanes bytes h
  rw [hout]
  exact (WP.spec_ok out).2 hval

theorem chunkValues_le_255 (c : Slice U8) (h : c.val.length = 4)
    (i : Fin 4) : chunkValues c i ≤ 255 := by
  have hi : i.val < c.val.length := by have := i.isLt; omega
  have hb : (c.val[i.val]).val ≤ 255 := by scalar_tac
  simpa [chunkValues, List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem hi] using hb

attribute [local step] u32x4_from_lanes_wp u32x4_add_assign_spec

theorem loop1_body_cons_spec (c : Slice U8)
    (cs : List (Slice U8)) (r : Slice U8)
    (A B : algo.U32X4) (k : Nat)
    (hsize : c.val.length = 4) (hk : k < 5552)
    (hA : ∀ i : Fin 4, laneValues A i ≤ aBound k)
    (hB : ∀ i : Fin 4, 2 * laneValues B i ≤ bBound2 k) :
    algo.Adler32.compute_loop1.body
        { chunks := c :: cs, remainder := r } A B
      ⦃ cf => ∃ A' B' : algo.U32X4,
        cf = .cont ({ chunks := cs, remainder := r }, A', B') ∧
        laneValues A' = laneAdd (laneValues A) (chunkValues c) ∧
        laneValues B' = laneAdd (laneValues B) (laneValues A') ⦄ := by
  have hAadd : ∀ i : Fin 4,
      laneValues A i + chunkValues c i ≤ U32.max := by
    intro i
    exact (laneBounds_step k _ _ _ hk (hA i) (hB i)
      (chunkValues_le_255 c hsize i)).1
  have hBadd : ∀ i : Fin 4,
      laneValues B i + (laneValues A i + chunkValues c i) ≤ U32.max := by
    intro i
    exact (laneBounds_step k _ _ _ hk (hA i) (hB i)
      (chunkValues_le_255 c hsize i)).2.1
  have hsize4 : 4 ≤ c.val.length := by omega
  simp only [algo.Adler32.compute_loop1.body,
    core.slice.iter.IteratorChunksExact.next, bind_ok]
  step with u32x4_from_lanes_wp
  step with u32x4_add_assign_spec
  · intro i
    change laneValues A i + laneValues cf i ≤ U32.max
    rw [cf_post]
    exact hAadd i
  step with u32x4_add_assign_spec
  · intro i
    change laneValues B i + laneValues a_vec1 i ≤ U32.max
    have hAi := a_vec1_post i
    change laneValues a_vec1 i = laneValues A i + laneValues cf i at hAi
    rw [hAi, cf_post]
    exact hBadd i
  refine ⟨a_vec1, b_vec1, rfl, ?_, ?_⟩
  · funext i
    change laneValues a_vec1 i =
      laneValues A i + chunkValues c i
    rw [show laneValues a_vec1 i = laneValues A i + laneValues cf i
        from a_vec1_post i, congrFun cf_post i]
  · funext i
    change laneValues b_vec1 i =
      laneValues B i + laneValues a_vec1 i
    exact b_vec1_post i

theorem loop1_nil (r : Slice U8) (A B : algo.U32X4) :
    algo.Adler32.compute_loop1
      { chunks := [], remainder := r } A B = .ok (A, B) := by
  unfold algo.Adler32.compute_loop1
  rw [loop.eq_1]
  simp [algo.Adler32.compute_loop1.body,
    core.slice.iter.IteratorChunksExact.next]

theorem result_ok_of_spec {α : Type _} (m : Result α) (p : α → Prop)
    (h : m ⦃ p ⦄) :
    ∃ x, m = .ok x ∧ p x := by
  cases m using Result.cases with
  | ret x => exact ⟨x, rfl, (WP.spec_ok x).mp h⟩
  | vis eff k => exact False.elim ((WP.spec_vis eff k).mp h)
  | div => exact False.elim (WP.spec_div.mp h)

theorem compute_loop1_spec (it : core.slice.iter.ChunksExact U8)
    (A B : algo.U32X4) (k : Nat)
    (hsize : ∀ c ∈ it.chunks, c.val.length = 4)
    (hcount : k + it.chunks.length ≤ 5552)
    (hA : ∀ i : Fin 4, laneValues A i ≤ aBound k)
    (hB : ∀ i : Fin 4, 2 * laneValues B i ≤ bBound2 k) :
    ∃ A' B' : algo.U32X4,
      algo.Adler32.compute_loop1 it A B = .ok (A', B') ∧
      (laneValues A', laneValues B') =
        it.chunks.foldl (fun st c => laneStep st (chunkValues c))
          (laneValues A, laneValues B) ∧
      (∀ i : Fin 4, laneValues A' i ≤ aBound (k + it.chunks.length)) ∧
      (∀ i : Fin 4, 2 * laneValues B' i ≤ bBound2 (k + it.chunks.length)) := by
  obtain ⟨chunks, r⟩ := it
  induction chunks generalizing A B k with
  | nil =>
    refine ⟨A, B, loop1_nil r A B, ?_, ?_, ?_⟩
    · rfl
    · simpa using hA
    · simpa using hB
  | cons c cs ih =>
    have hc : c.val.length = 4 := hsize c (by simp)
    have hcs : ∀ d ∈ cs, d.val.length = 4 := by
      intro d hd
      exact hsize d (by simp [hd])
    have hk : k < 5552 := by simp only [List.length_cons] at hcount; omega
    obtain ⟨flow, hflow, ⟨A1, B1, hcf, hAval, hBval⟩⟩ :=
      result_ok_of_spec _ _
        (loop1_body_cons_spec c cs r A B k hc hk hA hB)
    have hA1 : ∀ i : Fin 4, laneValues A1 i ≤ aBound (k + 1) := by
      intro i
      rw [congrFun hAval i]
      exact (laneBounds_step k _ _ _ hk (hA i) (hB i)
        (chunkValues_le_255 c hc i)).2.2.1
    have hB1 : ∀ i : Fin 4,
        2 * laneValues B1 i ≤ bBound2 (k + 1) := by
      intro i
      rw [congrFun hBval i]
      change 2 * (laneValues B i + laneValues A1 i) ≤ bBound2 (k + 1)
      rw [congrFun hAval i]
      change 2 * (laneValues B i + (laneValues A i + chunkValues c i)) ≤
        bBound2 (k + 1)
      exact (laneBounds_step k _ _ _ hk (hA i) (hB i)
        (chunkValues_le_255 c hc i)).2.2.2
    have hcount1 : k + 1 + cs.length ≤ 5552 := by
      simp only [List.length_cons] at hcount
      omega
    obtain ⟨A2, B2, hloop, hfold, hA2, hB2⟩ :=
      ih A1 B1 (k + 1) hA1 hB1 hcs hcount1
    refine ⟨A2, B2, ?_, ?_, ?_, ?_⟩
    · unfold algo.Adler32.compute_loop1
      rw [loop.eq_1]
      simp only [hflow, hcf, bind_ok]
      exact hloop
    · simp only [List.foldl_cons]
      simpa only [laneStep, hAval, hBval] using hfold
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hA2
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hB2

theorem compute_loop0_loop0_eq (it : core.slice.iter.ChunksExact U8)
    (A B : algo.U32X4) :
    algo.Adler32.compute_loop0_loop0 it A B =
      algo.Adler32.compute_loop1 it A B := by
  rfl

theorem compute_loop0_loop0_spec (it : core.slice.iter.ChunksExact U8)
    (A B : algo.U32X4) (k : Nat)
    (hsize : ∀ c ∈ it.chunks, c.val.length = 4)
    (hcount : k + it.chunks.length ≤ 5552)
    (hA : ∀ i : Fin 4, laneValues A i ≤ aBound k)
    (hB : ∀ i : Fin 4, 2 * laneValues B i ≤ bBound2 k) :
    ∃ A' B' : algo.U32X4,
      algo.Adler32.compute_loop0_loop0 it A B = .ok (A', B') ∧
      (laneValues A', laneValues B') =
        it.chunks.foldl (fun st c => laneStep st (chunkValues c))
          (laneValues A, laneValues B) ∧
      (∀ i : Fin 4, laneValues A' i ≤ aBound (k + it.chunks.length)) ∧
      (∀ i : Fin 4, 2 * laneValues B' i ≤ bBound2 (k + it.chunks.length)) := by
  rw [compute_loop0_loop0_eq]
  exact compute_loop1_spec it A B k hsize hcount hA hB

end adler2
