module
public import Proofs.ChunkLemmas

@[expose] public section
open Aeneas.Std
namespace adler2

theorem exact_chunks_flatten_length {α : Type _}
    (chunks : List (Slice α)) (n : Nat)
    (hlen : ∀ c ∈ chunks, c.val.length = n) :
    (chunks.map Slice.val).flatten.length = n * chunks.length := by
  induction chunks with
  | nil => simp
  | cons c cs ih =>
      have hc := hlen c (by simp)
      have hcs : ∀ d ∈ cs, d.val.length = n := by
        intro d hd
        exact hlen d (by simp [hd])
      simp only [List.map_cons, List.flatten_cons, List.length_append,
        List.length_cons, ih hcs]
      simp [Nat.mul_add]
      omega

theorem exact_chunks_count_bound {α : Type _} (s : Slice α)
    (iter : core.slice.iter.ChunksExact α) (n : Nat)
    (hlen : ∀ c ∈ iter.chunks, c.val.length = n)
    (hpart : (iter.chunks.map Slice.val).flatten ++ iter.remainder.val = s.val) :
    n * iter.chunks.length ≤ s.val.length := by
  have hflat := exact_chunks_flatten_length iter.chunks n hlen
  have hlen' := congrArg List.length hpart
  simp only [List.length_append] at hlen'
  omega

theorem prefix4_arithmetic (length : Nat) :
    (length - length % 4) % 4 = 0 ∧
    length - (length - length % 4) = length % 4 ∧
    length % 4 < 4 := by
  omega

theorem remainder_chunk_multiple4 {α : Type _} (s : Slice α)
    (iter : core.slice.iter.ChunksExact α)
    (hlen : ∀ c ∈ iter.chunks, c.val.length = 22208)
    (hpart : (iter.chunks.map Slice.val).flatten ++ iter.remainder.val = s.val)
    (hdiv : s.val.length % 4 = 0) :
    iter.remainder.val.length % 4 = 0 := by
  have hflat := exact_chunks_flatten_length iter.chunks 22208 hlen
  have hlen' := congrArg List.length hpart
  simp only [List.length_append] at hlen'
  omega

end adler2
