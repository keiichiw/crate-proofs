module
public import Proofs.IPv4SubnetEquality
public import Proofs.Comparisons

public section

/-! Derived value traits compare the stored fields in declaration order. They
apply to every raw range or iterator state, including reversed endpoints and
invalid minimum prefixes. -/
namespace IPv4IteratorDerived

open Aeneas Aeneas.Std Result

@[expose] def rangeKey (r : ipnet.ipext.Ipv4AddrRange) : Nat × Nat :=
  (CidrModel.ipv4Value r.start, CidrModel.ipv4Value r.end)

@[expose] def rangeCompare (a b : ipnet.ipext.Ipv4AddrRange) : Ordering :=
  match compare (rangeKey a).1 (rangeKey b).1 with
  | .lt => .lt
  | .eq => compare (rangeKey a).2 (rangeKey b).2
  | .gt => .gt

@[expose] def subnetsKey (r : ipnet.ipnet.Ipv4Subnets) : Nat × Nat × Nat :=
  (CidrModel.ipv4Value r.start, CidrModel.ipv4Value r.end, r.min_prefix_len.val)

@[expose] def subnetsCompare (a b : ipnet.ipnet.Ipv4Subnets) : Ordering :=
  match compare (subnetsKey a).1 (subnetsKey b).1 with
  | .lt => .lt
  | .eq =>
    match compare (subnetsKey a).2.1 (subnetsKey b).2.1 with
    | .lt => .lt
    | .eq => compare (subnetsKey a).2.2 (subnetsKey b).2.2
    | .gt => .gt
  | .gt => .gt

theorem range_clone_spec (r : ipnet.ipext.Ipv4AddrRange) :
    ipnet.ipext.Ipv4AddrRange.Insts.CoreCloneClone.clone r = Result.ok r := by
  rfl

theorem range_eq_spec (a b : ipnet.ipext.Ipv4AddrRange) :
    ∃ out, ipnet.ipext.Ipv4AddrRange.Insts.CoreCmpPartialEqIpv4AddrRange.eq a b =
      Result.ok out ∧ (out ↔ rangeKey a = rangeKey b) := by
  rcases IPv4SubnetStep.ipv4_eq_value a.start b.start with ⟨s, hs, hsi⟩
  by_cases h : s = true
  · have hv : CidrModel.ipv4Value a.start = CidrModel.ipv4Value b.start := hsi.mp h
    rcases IPv4SubnetStep.ipv4_eq_value a.end b.end with ⟨e, he, hei⟩
    refine ⟨e, ?_, ?_⟩
    · simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreCmpPartialEqIpv4AddrRange.eq, hs, h, he]
    · simp [rangeKey, hv, hei]
  · refine ⟨false, ?_, ?_⟩
    · simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreCmpPartialEqIpv4AddrRange.eq, hs, h]
    · have hv : CidrModel.ipv4Value a.start ≠ CidrModel.ipv4Value b.start := by
        intro heq
        exact h (hsi.mpr heq)
      simp [rangeKey, hv]

theorem range_cmp_spec (a b : ipnet.ipext.Ipv4AddrRange) :
    ipnet.ipext.Ipv4AddrRange.Insts.CoreCmpOrd.cmp a b =
      Result.ok (rangeCompare a b) := by
  simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreCmpOrd.cmp,
    Comparisons.ipv4_cmp_spec, rangeCompare, rangeKey, bind_ok]
  cases h : compare (CidrModel.ipv4Value a.start)
      (CidrModel.ipv4Value b.start) <;> simp

theorem range_partial_cmp_spec (a b : ipnet.ipext.Ipv4AddrRange) :
    ipnet.ipext.Ipv4AddrRange.Insts.CoreCmpPartialOrdIpv4AddrRange.partial_cmp a b =
      Result.ok (some (rangeCompare a b)) := by
  simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreCmpPartialOrdIpv4AddrRange.partial_cmp,
    range_cmp_spec, bind_ok]

theorem subnets_clone_spec (r : ipnet.ipnet.Ipv4Subnets) :
    ipnet.ipnet.Ipv4Subnets.Insts.CoreCloneClone.clone r = Result.ok r := by
  rfl

theorem subnets_eq_spec (a b : ipnet.ipnet.Ipv4Subnets) :
    ∃ out, ipnet.ipnet.Ipv4Subnets.Insts.CoreCmpPartialEqIpv4Subnets.eq a b =
      Result.ok out ∧ (out ↔ subnetsKey a = subnetsKey b) := by
  by_cases hq : a.min_prefix_len = b.min_prefix_len
  · rcases IPv4SubnetStep.ipv4_eq_value a.start b.start with ⟨s, hs, hsi⟩
    by_cases h : s = true
    · have hv : CidrModel.ipv4Value a.start = CidrModel.ipv4Value b.start := hsi.mp h
      rcases IPv4SubnetStep.ipv4_eq_value a.end b.end with ⟨e, he, hei⟩
      refine ⟨e, ?_, ?_⟩
      · simp [ipnet.ipnet.Ipv4Subnets.Insts.CoreCmpPartialEqIpv4Subnets.eq,
          hq, hs, h, he]
      · simp [subnetsKey, hv, hq, hei]
    · refine ⟨false, ?_, ?_⟩
      · simp [ipnet.ipnet.Ipv4Subnets.Insts.CoreCmpPartialEqIpv4Subnets.eq,
          hq, hs, h]
      · have hv : CidrModel.ipv4Value a.start ≠ CidrModel.ipv4Value b.start := by
          intro heq
          exact h (hsi.mpr heq)
        simp [subnetsKey, hv]
  · refine ⟨false, ?_, ?_⟩
    · simp [ipnet.ipnet.Ipv4Subnets.Insts.CoreCmpPartialEqIpv4Subnets.eq, hq]
    · have hqv : a.min_prefix_len.val ≠ b.min_prefix_len.val := by
        intro heq
        exact hq (UScalar.eq_of_val_eq heq)
      simp [subnetsKey, hqv]

theorem subnets_cmp_spec (a b : ipnet.ipnet.Ipv4Subnets) :
    ipnet.ipnet.Ipv4Subnets.Insts.CoreCmpOrd.cmp a b =
      Result.ok (subnetsCompare a b) := by
  simp [ipnet.ipnet.Ipv4Subnets.Insts.CoreCmpOrd.cmp,
    Comparisons.ipv4_cmp_spec, subnetsCompare, subnetsKey,
    core.cmp.impls.OrdU8.cmp, bind_ok]
  cases h : compare (CidrModel.ipv4Value a.start)
      (CidrModel.ipv4Value b.start) <;> simp
  cases h' : compare (CidrModel.ipv4Value a.end)
      (CidrModel.ipv4Value b.end) <;> simp

theorem subnets_partial_cmp_spec (a b : ipnet.ipnet.Ipv4Subnets) :
    ipnet.ipnet.Ipv4Subnets.Insts.CoreCmpPartialOrdIpv4Subnets.partial_cmp a b =
      Result.ok (some (subnetsCompare a b)) := by
  simp [ipnet.ipnet.Ipv4Subnets.Insts.CoreCmpPartialOrdIpv4Subnets.partial_cmp,
    subnets_cmp_spec, bind_ok]

end IPv4IteratorDerived
