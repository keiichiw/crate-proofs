import Aeneas
open Aeneas Aeneas.Std Result
namespace bytes_buffers

theorem setSlice_prefix_then_suffix {α : Type _} (dst first suffix : List α)
    (hlen : dst.length = first.length + suffix.length) :
    (dst.setSlice! 0 first).setSlice! first.length suffix = first ++ suffix := by
  have hp : first.length ≤ dst.length := by omega
  have hlen' : (dst.setSlice! 0 first).length = dst.length := List.length_setSlice! _ _ _
  have hfirst : (dst.setSlice! 0 first).take first.length = first := by
    simp [List.setSlice!,Nat.min_eq_left hp]
  rw [List.setSlice!]
  rw [hlen',show dst.length-first.length=suffix.length by omega,Nat.min_self,
    List.take_length,hfirst]
  have hdrop : (dst.setSlice! 0 first).drop (first.length + suffix.length) = [] := by
    apply List.drop_eq_nil_of_le
    omega
  rw [hdrop,List.append_nil]

theorem copy_fragment_completion {α : Type _} (dst src view : List α) (k : Nat)
    (hprefix : src.IsPrefix view) (hkdst : k ≤ dst.length) (hksrc : k ≤ src.length)
    (hfit : dst.length ≤ view.length) :
    (dst.setSlice! 0 (src.take k)).setSlice! k
      ((view.drop k).take (dst.length-k)) = view.take dst.length := by
  have hkview : k ≤ view.length := le_trans hksrc hprefix.length_le
  have htake : src.take k = view.take k := by
    obtain ⟨tail,htail⟩ := hprefix
    rw [← htail,List.take_append_of_le_length hksrc]
  have hprefixlen : (src.take k).length = k := by simp [List.length_take,Nat.min_eq_left hksrc]
  have hsuffixlen : ((view.drop k).take (dst.length-k)).length = dst.length-k := by
    simp only [List.length_take,List.length_drop]
    omega
  have heq := setSlice_prefix_then_suffix dst (src.take k)
    ((view.drop k).take (dst.length-k)) (by rw [hprefixlen,hsuffixlen]; omega)
  rw [hprefixlen] at heq
  rw [heq,htake]
  rw [← List.take_add]
  congr 1
  omega
end bytes_buffers
