module
public import Aeneas.Std.SliceIter

@[expose] public section
open Aeneas.Std

namespace adler2

variable {α : Type _}

theorem chunksExact_length {n : Nat} (hn : 0 < n) (l : List α) :
    ∀ c ∈ (List.toChunksExact n hn l).1, c.length = n := by
  unfold List.toChunksExact
  split
  · simp
  · simp only [List.mem_cons]
    intro c hc
    rcases hc with rfl | hc
    · simp [List.length_take]
      omega
    · exact chunksExact_length hn _ c hc
termination_by l.length
decreasing_by simp [List.length_drop]; omega

theorem chunksExact_remainder_lt {n : Nat} (hn : 0 < n) (l : List α) :
    (List.toChunksExact n hn l).2.length < n := by
  unfold List.toChunksExact
  split
  · assumption
  · exact chunksExact_remainder_lt hn (l.drop n)
termination_by l.length
decreasing_by simp [List.length_drop]; omega

theorem chunksExact_partition {n : Nat} (hn : 0 < n) (l : List α) :
    (List.toChunksExact n hn l).1.flatten ++ (List.toChunksExact n hn l).2 = l := by
  unfold List.toChunksExact
  split
  · simp
  · simp only [List.flatten_cons, List.append_assoc]
    rw [chunksExact_partition hn (l.drop n)]
    exact List.take_append_drop n l
termination_by l.length
decreasing_by simp [List.length_drop]; omega


theorem sliceChunksExact_partition {α : Type _} (s : Slice α) (n : Usize)
    (hn : 0 < n.val) :
    ∃ iter : core.slice.iter.ChunksExact α,
      core.slice.Slice.chunks_exact s n = .ok iter ∧
      (∀ c ∈ iter.chunks, c.val.length = n.val) ∧
      iter.remainder.val.length < n.val ∧
      (iter.chunks.map Slice.val).flatten ++ iter.remainder.val = s.val := by
  simp only [core.slice.Slice.chunks_exact, dite_eq_left hn]
  let r := List.toChunksExact n.val hn s.val
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_map] at hc
    rcases hc with ⟨d, hd, rfl⟩
    simpa only [Slice.from_val] using chunksExact_length hn s.val d.val d.property
  · simpa only [Slice.from_val] using chunksExact_remainder_lt hn s.val
  · simp only [List.map_map, Function.comp_def, Slice.from_val, List.attach_map_subtype_val]
    exact chunksExact_partition hn s.val


theorem chunksExact_getRemainder {α : Type _}
    (iter : core.slice.iter.ChunksExact α) :
    core.slice.iter.ChunksExact.getRemainder iter = .ok iter.remainder := rfl

theorem chunksExact_next_cons {α : Type _} (c : Slice α)
    (cs : List (Slice α)) (r : Slice α) :
    core.slice.iter.IteratorChunksExact.next
        { chunks := c :: cs, remainder := r } =
      .ok (some c, { chunks := cs, remainder := r }) := rfl

theorem chunksExact_next_nil {α : Type _} (r : Slice α) :
    core.slice.iter.IteratorChunksExact.next
        { chunks := [], remainder := r } =
      .ok (none, { chunks := [], remainder := r }) := rfl

end adler2
