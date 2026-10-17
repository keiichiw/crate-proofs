module
public import Adler2

public section

open Aeneas.Std

namespace adler2

theorem u32x4_from_spec (bytes : Slice U8) (h : 4 ≤ bytes.val.length) :
    ∃ out : algo.U32X4,
      algo.U32X4.from bytes = Result.ok out ∧
      out.val.map (fun x => x.val) = (bytes.val.take 4).map (fun x => x.val) := by
  have h0 : 0 < bytes.val.length := by omega
  have h1 : 1 < bytes.val.length := by omega
  have h2 : 2 < bytes.val.length := by omega
  have h3 : 3 < bytes.val.length := by omega
  have i0 : Slice.index_usize bytes 0#usize = Result.ok bytes.val[0] := by
    simp [Slice.index_usize, Slice.getElem?_Usize_eq, List.getElem?_eq_getElem h0]
  have i1 : Slice.index_usize bytes 1#usize = Result.ok bytes.val[1] := by
    simp [Slice.index_usize, Slice.getElem?_Usize_eq, List.getElem?_eq_getElem h1]
  have i2 : Slice.index_usize bytes 2#usize = Result.ok bytes.val[2] := by
    simp [Slice.index_usize, Slice.getElem?_Usize_eq, List.getElem?_eq_getElem h2]
  have i3 : Slice.index_usize bytes 3#usize = Result.ok bytes.val[3] := by
    simp [Slice.index_usize, Slice.getElem?_Usize_eq, List.getElem?_eq_getElem h3]
  simp only [algo.U32X4.from, i0, i1, i2, i3, lift, bind_ok]
  refine ⟨_, rfl, ?_⟩
  simp only [Array.make_val, List.map_cons, List.map_nil,
    core.convert.num.FromU32U8.from_val_eq]
  have htake : bytes.val.take 4 =
      [bytes.val[0], bytes.val[1], bytes.val[2], bytes.val[3]] := by
    rw [List.take_succ_eq_append_getElem h3]
    rw [List.take_succ_eq_append_getElem h2]
    rw [List.take_succ_eq_append_getElem h1]
    rw [List.take_succ_eq_append_getElem h0]
    simp
  rw [htake]
  simp

end adler2
