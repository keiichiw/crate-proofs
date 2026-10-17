module
public import Proofs.Compute
public import Proofs.Codec
public import Proofs.Smoke

public section

open Aeneas.Std

namespace adler2

private theorem observe_injective {s t : Adler32}
    (h : observe s = observe t) : s = t := by
  cases s with
  | mk a b =>
    cases t with
    | mk a' b' =>
      simp only [observe, Prod.mk.injEq] at h
      obtain ⟨ha, hb⟩ := h
      simp only [Adler32.mk.injEq]
      exact ⟨UScalar.eq_imp _ _ ha, UScalar.eq_imp _ _ hb⟩

theorem write_slice_spec (s : Adler32) (bytes : Slice U8) :
    ∃ out : Adler32,
      Adler32.write_slice s bytes = .ok out ∧
      observe out = run (observe s) bytes.val := by
  obtain ⟨out, hout, hobs⟩ := compute_spec s bytes
  exact ⟨out, hout, hobs⟩

theorem adler32_slice_spec (data : Slice U8) :
    ∃ out : U32,
      adler32_slice data = .ok out ∧
      out.val = encode (run (1, 0) data.val) := by
  let initial : Adler32 := { a := 1#u16, b := 0#u16 }
  obtain ⟨updated, hwrite, hobs⟩ :=
    write_slice_spec initial data
  obtain ⟨out, hchecksum, hval⟩ := checksum_spec updated
  refine ⟨out, ?_, ?_⟩
  · dsimp [initial] at hwrite
    simp only [adler32_slice, new_spec, bind_ok, hwrite, hchecksum]
  · change out.val = encode (observe updated) at hval
    rw [hval, hobs]
    rfl

theorem split_update_spec (s : Adler32)
    (xs ys whole : Slice U8) (hwhole : whole.val = xs.val ++ ys.val) :
    ∃ mid final wholeOut : Adler32,
      Adler32.write_slice s xs = .ok mid ∧
      Adler32.write_slice mid ys = .ok final ∧
      Adler32.write_slice s whole = .ok wholeOut ∧
      final = wholeOut := by
  obtain ⟨mid, hmid, hmidObs⟩ :=
    write_slice_spec s xs
  obtain ⟨final, hfinal, hfinalObs⟩ :=
    write_slice_spec mid ys
  obtain ⟨wholeOut, hwholeOut, hwholeObs⟩ :=
    write_slice_spec s whole
  refine ⟨mid, final, wholeOut, hmid, hfinal, hwholeOut, ?_⟩
  apply observe_injective
  rw [hfinalObs, hmidObs, hwholeObs, hwhole, run_append]

theorem write_slice_append_spec (s : Adler32)
    (xs ys whole : Slice U8) (hwhole : whole.val = xs.val ++ ys.val) :
    ∃ out : Adler32,
      Adler32.write_slice s whole = .ok out ∧
      (do
        let mid ← Adler32.write_slice s xs
        Adler32.write_slice mid ys) = .ok out := by
  obtain ⟨mid, final, wholeOut, hmid, hfinal, hwholeOut, heq⟩ :=
    split_update_spec s xs ys whole hwhole
  refine ⟨wholeOut, hwholeOut, ?_⟩
  simp [hmid, hfinal, heq]

theorem write_slice_resume_spec (s : Adler32)
    (xs ys whole : Slice U8) (hwhole : whole.val = xs.val ++ ys.val) :
    ∃ out : Adler32,
      Adler32.write_slice s whole = .ok out ∧
      (do
        let mid ← Adler32.write_slice s xs
        let sum ← Adler32.checksum mid
        let restored ← Adler32.from_checksum sum
        Adler32.write_slice restored ys) = .ok out := by
  obtain ⟨mid, final, wholeOut, hmid, hfinal, hwholeOut, heq⟩ :=
    split_update_spec s xs ys whole hwhole
  obtain ⟨sum, hsum, _⟩ := checksum_spec mid
  have hrestore : Adler32.from_checksum sum = .ok mid := by
    have hround := from_checksum_checksum mid
    rw [hsum] at hround
    simpa using hround
  refine ⟨wholeOut, hwholeOut, ?_⟩
  simp [hmid, hsum, hrestore, hfinal, heq]

theorem resume_checksum_spec (sum : U32) (bytes : Slice U8) :
    ∃ out : U32,
      (do
        let s ← Adler32.from_checksum sum
        let updated ← Adler32.write_slice s bytes
        Adler32.checksum updated) = .ok out ∧
      out.val = encode (run (sum.val % 65536, sum.val / 65536) bytes.val) := by
  obtain ⟨s, hs, ha, hb⟩ := from_checksum_spec sum
  obtain ⟨updated, hwrite, hobs⟩ :=
    write_slice_spec s bytes
  obtain ⟨out, hchecksum, hval⟩ := checksum_spec updated
  refine ⟨out, ?_, ?_⟩
  · simp [hs, hwrite, hchecksum]
  · change out.val = encode (observe updated) at hval
    rw [hval, hobs]
    simp only [observe, ha, hb]

end adler2
