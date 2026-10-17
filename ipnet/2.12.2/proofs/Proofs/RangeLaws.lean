module
public import Proofs.RangeNext

public section

namespace RangeLaws

open Aeneas Aeneas.Std

private theorem model_of_success (r : ipnet.ipext.Ipv4AddrRange)
    (out : Option ipnet.core.net.ip_addr.Ipv4Addr)
    (r' : ipnet.ipext.Ipv4AddrRange)
    (hexec : ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.next r =
      Result.ok (out, r')) :
    (out.map CidrModel.ipv4Value, RangeNext.remaining r') =
      RangeMath.next (RangeNext.remaining r) := by
  rcases RangeNext.range_next_spec r with ⟨out₀, r₀, hrun, hmodel⟩
  rw [hexec] at hrun
  have hp := Result.ok_injective hrun
  obtain ⟨hout, hr⟩ := Prod.mk.inj hp
  simpa [hout, hr] using hmodel

/-- Actual `next` returns `none` exactly when the independent remaining range is empty. -/
theorem next_none_iff_empty (r : ipnet.ipext.Ipv4AddrRange)
    (out : Option ipnet.core.net.ip_addr.Ipv4Addr)
    (r' : ipnet.ipext.Ipv4AddrRange)
    (hexec : ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.next r =
      Result.ok (out, r')) :
    out = none ↔ RangeNext.remaining r = .empty := by
  have hm := model_of_success r out r' hexec
  let s := CidrModel.ipv4Value r.start
  let e := CidrModel.ipv4Value r.end
  have hf := congrArg Prod.fst hm
  change out.map CidrModel.ipv4Value =
    (RangeMath.next (RangeMath.ofInclusive s e)).1 at hf
  constructor
  · intro hout
    rw [hout] at hf
    have hgt := (RangeMath.next_none_iff s e).mp hf.symm
    exact (RangeMath.ofInclusive_empty_iff s e).mpr hgt
  · intro hempty
    have hgt := (RangeMath.ofInclusive_empty_iff s e).mp hempty
    have hn := (RangeMath.next_none_iff s e).mpr hgt
    rw [hn] at hf
    cases out with
    | none => rfl
    | some _ => simp at hf

/-- On a successful `some`, the returned address is the least member; the
    residual range excludes it, has one fewer member, and partitions the old range. -/
theorem next_some_laws (r : ipnet.ipext.Ipv4AddrRange)
    (a : ipnet.core.net.ip_addr.Ipv4Addr)
    (r' : ipnet.ipext.Ipv4AddrRange)
    (hexec : ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.next r =
      Result.ok (some a, r')) :
    CidrModel.ipv4Value a = CidrModel.ipv4Value r.start ∧
      RangeMath.size (RangeNext.remaining r') + 1 =
        RangeMath.size (RangeNext.remaining r) ∧
      (∀ x, RangeMath.mem (RangeNext.remaining r) x ↔
        x = CidrModel.ipv4Value a ∨ RangeMath.mem (RangeNext.remaining r') x) ∧
      ¬ RangeMath.mem (RangeNext.remaining r') (CidrModel.ipv4Value a) := by
  have hm := model_of_success r (some a) r' hexec
  let s := CidrModel.ipv4Value r.start
  let e := CidrModel.ipv4Value r.end
  have hf := congrArg Prod.fst hm
  have hs := congrArg Prod.snd hm
  change some (CidrModel.ipv4Value a) =
    (RangeMath.next (RangeMath.ofInclusive s e)).1 at hf
  change RangeNext.remaining r' =
    (RangeMath.next (RangeMath.ofInclusive s e)).2 at hs
  have hle : s ≤ e := by
    by_contra h
    have hgt : e < s := by omega
    rw [RangeMath.next_gt s e hgt] at hf
    contradiction
  have hnext := RangeMath.next_some_size s e hle
  have ha : CidrModel.ipv4Value a = s := by
    rw [hnext.1] at hf
    exact Option.some.inj hf
  refine ⟨ha, ?_, ?_, ?_⟩
  · rw [hs]
    exact hnext.2
  · intro x
    rw [hs, ha]
    exact RangeMath.next_partition s e x hle
  · rw [hs, ha]
    exact RangeMath.next_residual_excludes_head s e hle

/-- An empty raw state produces `none` and stays abstractly empty. -/
theorem next_empty_preserved (r : ipnet.ipext.Ipv4AddrRange)
    (h : RangeNext.remaining r = .empty) :
    ∃ r',
      ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.next r =
        Result.ok (none, r') ∧
      RangeNext.remaining r' = .empty := by
  rcases RangeNext.range_next_spec r with ⟨out, r', hexec, hm⟩
  rw [h, RangeMath.next_empty] at hm
  have hout : out = none := by
    cases out with
    | none => rfl
    | some _ => simp at hm
  refine ⟨r', ?_, ?_⟩
  · simpa [hout] using hexec
  · exact (congrArg Prod.snd hm)

/-- A second actual `next` after `none` also returns `none`; no elements revive. -/
theorem next_none_no_revival (r : ipnet.ipext.Ipv4AddrRange)
    (r' : ipnet.ipext.Ipv4AddrRange)
    (hexec : ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.next r =
      Result.ok (none, r')) :
    ∃ r'',
      ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.next r' =
        Result.ok (none, r'') ∧
      RangeNext.remaining r'' = .empty := by
  have h : RangeNext.remaining r = .empty :=
    (next_none_iff_empty r none r' hexec).mp rfl
  have hm := model_of_success r none r' hexec
  rw [h, RangeMath.next_empty] at hm
  have h' : RangeNext.remaining r' = .empty := congrArg Prod.snd hm
  exact next_empty_preserved r' h'

/-- A finite sequence of actual `next` calls, each returning `none`. -/
inductive NoneSteps : Nat → ipnet.ipext.Ipv4AddrRange →
    ipnet.ipext.Ipv4AddrRange → Prop where
  | zero (r) : NoneSteps 0 r r
  | succ {n r r' r''}
      (hnext : ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.next r =
        Result.ok (none, r'))
      (hrest : NoneSteps n r' r'') : NoneSteps (n + 1) r r''

/-- No finite number of additional actual `next` calls revives an empty range. -/
theorem finite_no_revival (n : Nat) (r : ipnet.ipext.Ipv4AddrRange)
    (h : RangeNext.remaining r = .empty) :
    ∃ r', NoneSteps n r r' ∧ RangeNext.remaining r' = .empty := by
  induction n generalizing r with
  | zero =>
    exact ⟨r, NoneSteps.zero r, h⟩
  | succ n ih =>
    rcases next_empty_preserved r h with ⟨r₁, hnext, h₁⟩
    rcases ih r₁ h₁ with ⟨r₂, hsteps, h₂⟩
    exact ⟨r₂, NoneSteps.succ hnext hsteps, h₂⟩

end RangeLaws
