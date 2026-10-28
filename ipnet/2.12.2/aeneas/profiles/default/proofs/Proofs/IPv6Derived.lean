module
public import Proofs.IPv6AddressEq
public import Proofs.Comparisons

public section

/-! Derived value traits compare the stored fields in declaration order. They
apply to every raw range or iterator state, including reversed endpoints and
invalid minimum prefixes. -/
namespace IPv6Derived

open Aeneas Aeneas.Std Result

@[expose] def netKey (n : ipnet.ipnet.Ipv6Net) : Nat × Nat :=
  (CidrModel.ipv6Value n.addr, n.prefix_len.val)

@[expose] def netCompare (a b : ipnet.ipnet.Ipv6Net) : Ordering :=
  match compare (netKey a).1 (netKey b).1 with
  | .lt => .lt
  | .eq => compare (netKey a).2 (netKey b).2
  | .gt => .gt

theorem net_clone_spec (n : ipnet.ipnet.Ipv6Net) :
    ipnet.ipnet.Ipv6Net.Insts.CoreCloneClone.clone n = Result.ok n := by
  rfl

theorem net_eq_spec (a b : ipnet.ipnet.Ipv6Net) :
    ∃ out, ipnet.ipnet.Ipv6Net.Insts.CoreCmpPartialEqIpv6Net.eq a b =
      Result.ok out ∧ (out ↔ netKey a = netKey b) := by
  rcases IPv6AddressEq.ipv6_eq_value a.addr b.addr with ⟨out, hout, hiff⟩
  by_cases hp : a.prefix_len = b.prefix_len
  · refine ⟨out, ?_, ?_⟩
    · simp [ipnet.ipnet.Ipv6Net.Insts.CoreCmpPartialEqIpv6Net.eq, hp, hout]
    · simp [netKey, hp, hiff]
  · refine ⟨false, ?_, ?_⟩
    · simp [ipnet.ipnet.Ipv6Net.Insts.CoreCmpPartialEqIpv6Net.eq, hp]
    · have hpval : a.prefix_len.val ≠ b.prefix_len.val := by
        intro h
        exact hp (UScalar.eq_of_val_eq h)
      simp [netKey, hpval]

theorem net_cmp_spec (a b : ipnet.ipnet.Ipv6Net) :
    ipnet.ipnet.Ipv6Net.Insts.CoreCmpOrd.cmp a b =
      Result.ok (netCompare a b) := by
  simp [ipnet.ipnet.Ipv6Net.Insts.CoreCmpOrd.cmp,
    Comparisons.ipv6_cmp_spec, netCompare, netKey,
    core.cmp.impls.OrdU8.cmp, bind_ok]
  cases h : compare (CidrModel.ipv6Value a.addr)
      (CidrModel.ipv6Value b.addr) <;> simp

theorem net_partial_cmp_spec (a b : ipnet.ipnet.Ipv6Net) :
    ipnet.ipnet.Ipv6Net.Insts.CoreCmpPartialOrdIpv6Net.partial_cmp a b =
      Result.ok (some (netCompare a b)) := by
  simp [ipnet.ipnet.Ipv6Net.Insts.CoreCmpPartialOrdIpv6Net.partial_cmp,
    net_cmp_spec, bind_ok]

@[expose] def rangeKey (r : ipnet.ipext.Ipv6AddrRange) : Nat × Nat :=
  (CidrModel.ipv6Value r.start, CidrModel.ipv6Value r.end)

@[expose] def rangeCompare (a b : ipnet.ipext.Ipv6AddrRange) : Ordering :=
  match compare (rangeKey a).1 (rangeKey b).1 with
  | .lt => .lt
  | .eq => compare (rangeKey a).2 (rangeKey b).2
  | .gt => .gt

@[expose] def subnetsKey (r : ipnet.ipnet.Ipv6Subnets) : Nat × Nat × Nat :=
  (CidrModel.ipv6Value r.start, CidrModel.ipv6Value r.end, r.min_prefix_len.val)

@[expose] def subnetsCompare (a b : ipnet.ipnet.Ipv6Subnets) : Ordering :=
  match compare (subnetsKey a).1 (subnetsKey b).1 with
  | .lt => .lt
  | .eq =>
    match compare (subnetsKey a).2.1 (subnetsKey b).2.1 with
    | .lt => .lt
    | .eq => compare (subnetsKey a).2.2 (subnetsKey b).2.2
    | .gt => .gt
  | .gt => .gt

theorem range_clone_spec (r : ipnet.ipext.Ipv6AddrRange) :
    ipnet.ipext.Ipv6AddrRange.Insts.CoreCloneClone.clone r = Result.ok r := by
  rfl

theorem range_eq_spec (a b : ipnet.ipext.Ipv6AddrRange) :
    ∃ out, ipnet.ipext.Ipv6AddrRange.Insts.CoreCmpPartialEqIpv6AddrRange.eq a b =
      Result.ok out ∧ (out ↔ rangeKey a = rangeKey b) := by
  rcases IPv6AddressEq.ipv6_eq_value a.start b.start with ⟨s, hs, hsi⟩
  by_cases h : s = true
  · have hv : CidrModel.ipv6Value a.start = CidrModel.ipv6Value b.start := hsi.mp h
    rcases IPv6AddressEq.ipv6_eq_value a.end b.end with ⟨e, he, hei⟩
    refine ⟨e, ?_, ?_⟩
    · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreCmpPartialEqIpv6AddrRange.eq, hs, h, he]
    · simp [rangeKey, hv, hei]
  · refine ⟨false, ?_, ?_⟩
    · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreCmpPartialEqIpv6AddrRange.eq, hs, h]
    · have hv : CidrModel.ipv6Value a.start ≠ CidrModel.ipv6Value b.start := by
        intro heq
        exact h (hsi.mpr heq)
      simp [rangeKey, hv]

theorem range_cmp_spec (a b : ipnet.ipext.Ipv6AddrRange) :
    ipnet.ipext.Ipv6AddrRange.Insts.CoreCmpOrd.cmp a b =
      Result.ok (rangeCompare a b) := by
  simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreCmpOrd.cmp,
    Comparisons.ipv6_cmp_spec, rangeCompare, rangeKey, bind_ok]
  cases h : compare (CidrModel.ipv6Value a.start)
      (CidrModel.ipv6Value b.start) <;> simp

theorem range_partial_cmp_spec (a b : ipnet.ipext.Ipv6AddrRange) :
    ipnet.ipext.Ipv6AddrRange.Insts.CoreCmpPartialOrdIpv6AddrRange.partial_cmp a b =
      Result.ok (some (rangeCompare a b)) := by
  simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreCmpPartialOrdIpv6AddrRange.partial_cmp,
    range_cmp_spec, bind_ok]

theorem subnets_clone_spec (r : ipnet.ipnet.Ipv6Subnets) :
    ipnet.ipnet.Ipv6Subnets.Insts.CoreCloneClone.clone r = Result.ok r := by
  rfl

theorem subnets_eq_spec (a b : ipnet.ipnet.Ipv6Subnets) :
    ∃ out, ipnet.ipnet.Ipv6Subnets.Insts.CoreCmpPartialEqIpv6Subnets.eq a b =
      Result.ok out ∧ (out ↔ subnetsKey a = subnetsKey b) := by
  by_cases hq : a.min_prefix_len = b.min_prefix_len
  · rcases IPv6AddressEq.ipv6_eq_value a.start b.start with ⟨s, hs, hsi⟩
    by_cases h : s = true
    · have hv : CidrModel.ipv6Value a.start = CidrModel.ipv6Value b.start := hsi.mp h
      rcases IPv6AddressEq.ipv6_eq_value a.end b.end with ⟨e, he, hei⟩
      refine ⟨e, ?_, ?_⟩
      · simp [ipnet.ipnet.Ipv6Subnets.Insts.CoreCmpPartialEqIpv6Subnets.eq,
          hq, hs, h, he]
      · simp [subnetsKey, hv, hq, hei]
    · refine ⟨false, ?_, ?_⟩
      · simp [ipnet.ipnet.Ipv6Subnets.Insts.CoreCmpPartialEqIpv6Subnets.eq,
          hq, hs, h]
      · have hv : CidrModel.ipv6Value a.start ≠ CidrModel.ipv6Value b.start := by
          intro heq
          exact h (hsi.mpr heq)
        simp [subnetsKey, hv]
  · refine ⟨false, ?_, ?_⟩
    · simp [ipnet.ipnet.Ipv6Subnets.Insts.CoreCmpPartialEqIpv6Subnets.eq, hq]
    · have hqv : a.min_prefix_len.val ≠ b.min_prefix_len.val := by
        intro heq
        exact hq (UScalar.eq_of_val_eq heq)
      simp [subnetsKey, hqv]

theorem subnets_cmp_spec (a b : ipnet.ipnet.Ipv6Subnets) :
    ipnet.ipnet.Ipv6Subnets.Insts.CoreCmpOrd.cmp a b =
      Result.ok (subnetsCompare a b) := by
  simp [ipnet.ipnet.Ipv6Subnets.Insts.CoreCmpOrd.cmp,
    Comparisons.ipv6_cmp_spec, subnetsCompare, subnetsKey,
    core.cmp.impls.OrdU8.cmp, bind_ok]
  cases h : compare (CidrModel.ipv6Value a.start)
      (CidrModel.ipv6Value b.start) <;> simp
  cases h' : compare (CidrModel.ipv6Value a.end)
      (CidrModel.ipv6Value b.end) <;> simp

theorem subnets_partial_cmp_spec (a b : ipnet.ipnet.Ipv6Subnets) :
    ipnet.ipnet.Ipv6Subnets.Insts.CoreCmpPartialOrdIpv6Subnets.partial_cmp a b =
      Result.ok (some (subnetsCompare a b)) := by
  simp [ipnet.ipnet.Ipv6Subnets.Insts.CoreCmpPartialOrdIpv6Subnets.partial_cmp,
    subnets_cmp_spec, bind_ok]

end IPv6Derived
