module
public import Proofs.ChunkLemmas

@[expose] public section

open Aeneas Aeneas.Std

namespace adler2

theorem length_flatten_exact {α : Type _} (n : Nat)
    (groups : List (List α)) (hsize : ∀ g ∈ groups, g.length = n) :
    groups.flatten.length = n * groups.length := by
  induction groups with
  | nil => simp
  | cons g gs ih =>
    have hg : g.length = n := hsize g (by simp)
    have hgs : ∀ h ∈ gs, h.length = n := by
      intro h hh
      exact hsize h (by simp [hh])
    simp [hg, ih hgs, Nat.mul_succ, Nat.add_comm]

theorem sliceChunks4_spec (s : Slice U8)
    (hdiv : s.val.length % 4 = 0) :
    ∃ iter : core.slice.iter.ChunksExact U8,
      core.slice.Slice.chunks_exact s 4#usize = .ok iter ∧
      (∀ c ∈ iter.chunks, c.val.length = 4) ∧
      iter.remainder.val = [] ∧
      iter.chunks.length = s.val.length / 4 ∧
      (iter.chunks.map Slice.val).flatten = s.val := by
  have hfour : (4#usize).val = 4 := by decide
  have hpos : 0 < (4#usize).val := by decide
  obtain ⟨iter, hiter, hsize, hrem, hpartition⟩ :=
    sliceChunksExact_partition s 4#usize hpos
  have hsize4 : ∀ c ∈ iter.chunks, c.val.length = 4 := by
    simpa only [hfour] using hsize
  have hflat : (iter.chunks.map Slice.val).flatten.length =
      4 * iter.chunks.length := by
    have h := length_flatten_exact 4 (iter.chunks.map Slice.val) (by
      intro g hg
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hg
      exact hsize4 c hc)
    simpa only [List.length_map] using h
  have hlen : s.val.length = 4 * iter.chunks.length + iter.remainder.val.length := by
    rw [← hpartition, List.length_append, hflat]
  have hrem4 : iter.remainder.val.length < 4 := by
    simpa only [hfour] using hrem
  have hempty : iter.remainder.val = [] := by
    have : iter.remainder.val.length = 0 := by omega
    exact List.length_eq_zero_iff.mp this
  have hcount : iter.chunks.length = s.val.length / 4 := by omega
  refine ⟨iter, hiter, hsize4, hempty, hcount, ?_⟩
  simpa only [hempty, List.append_nil] using hpartition

theorem sliceChunks4_full (s : Slice U8) (hlen : s.val.length = 22208) :
    ∃ iter : core.slice.iter.ChunksExact U8,
      core.slice.Slice.chunks_exact s 4#usize = .ok iter ∧
      (∀ c ∈ iter.chunks, c.val.length = 4) ∧
      iter.remainder.val = [] ∧
      iter.chunks.length = 5552 ∧
      (iter.chunks.map Slice.val).flatten = s.val := by
  have hdiv : s.val.length % 4 = 0 := by omega
  obtain ⟨iter, hiter, hsize, hrem, hcount, hpartition⟩ :=
    sliceChunks4_spec s hdiv
  refine ⟨iter, hiter, hsize, hrem, ?_, hpartition⟩
  omega

theorem sliceChunks4_short (s : Slice U8)
    (hdiv : s.val.length % 4 = 0) (hlen : s.val.length < 22208) :
    ∃ iter : core.slice.iter.ChunksExact U8,
      core.slice.Slice.chunks_exact s 4#usize = .ok iter ∧
      (∀ c ∈ iter.chunks, c.val.length = 4) ∧
      iter.remainder.val = [] ∧
      iter.chunks.length ≤ 5551 ∧
      (iter.chunks.map Slice.val).flatten = s.val := by
  obtain ⟨iter, hiter, hsize, hrem, hcount, hpartition⟩ :=
    sliceChunks4_spec s hdiv
  refine ⟨iter, hiter, hsize, hrem, ?_, hpartition⟩
  omega

end adler2
