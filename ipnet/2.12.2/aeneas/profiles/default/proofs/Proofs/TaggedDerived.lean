module
public import Proofs.IPv4Derived
public import Proofs.IPv4IteratorDerived
public import Proofs.IPv6Derived

public section

namespace TaggedDerived

open Aeneas Aeneas.Std Result

/-! The first component is the declared family rank. The remaining components
are independent network-order address values and stored scalar fields. -/
@[expose] def netKey : ipnet.ipnet.IpNet → Nat × Nat × Nat
  | .V4 n => (0, CidrModel.ipv4Value n.addr, n.prefix_len.val)
  | .V6 n => (1, CidrModel.ipv6Value n.addr, n.prefix_len.val)

@[expose] def rangeKey : ipnet.ipext.IpAddrRange → Nat × Nat × Nat
  | .V4 r => (0, CidrModel.ipv4Value r.start, CidrModel.ipv4Value r.end)
  | .V6 r => (1, CidrModel.ipv6Value r.start, CidrModel.ipv6Value r.end)

@[expose] def subnetsKey : ipnet.ipnet.IpSubnets → Nat × Nat × Nat × Nat
  | .V4 r => (0, CidrModel.ipv4Value r.start,
      CidrModel.ipv4Value r.end, r.min_prefix_len.val)
  | .V6 r => (1, CidrModel.ipv6Value r.start,
      CidrModel.ipv6Value r.end, r.min_prefix_len.val)

@[expose] def netCompare (a b : ipnet.ipnet.IpNet) : Ordering :=
  match a, b with
  | .V4 x, .V4 y => IPv4Derived.keyCompare x y
  | .V4 _, .V6 _ => .lt
  | .V6 _, .V4 _ => .gt
  | .V6 x, .V6 y => IPv6Derived.netCompare x y

@[expose] def rangeCompare (a b : ipnet.ipext.IpAddrRange) : Ordering :=
  match a, b with
  | .V4 x, .V4 y => IPv4IteratorDerived.rangeCompare x y
  | .V4 _, .V6 _ => .lt
  | .V6 _, .V4 _ => .gt
  | .V6 x, .V6 y => IPv6Derived.rangeCompare x y

@[expose] def subnetsCompare (a b : ipnet.ipnet.IpSubnets) : Ordering :=
  match a, b with
  | .V4 x, .V4 y => IPv4IteratorDerived.subnetsCompare x y
  | .V4 _, .V6 _ => .lt
  | .V6 _, .V4 _ => .gt
  | .V6 x, .V6 y => IPv6Derived.subnetsCompare x y

theorem net_clone_spec (n : ipnet.ipnet.IpNet) :
    ipnet.ipnet.IpNet.Insts.CoreCloneClone.clone n = Result.ok n := by
  rfl

theorem range_clone_spec (r : ipnet.ipext.IpAddrRange) :
    ipnet.ipext.IpAddrRange.Insts.CoreCloneClone.clone r = Result.ok r := by
  rfl

theorem subnets_clone_spec (r : ipnet.ipnet.IpSubnets) :
    ipnet.ipnet.IpSubnets.Insts.CoreCloneClone.clone r = Result.ok r := by
  rfl

theorem net_eq_spec (a b : ipnet.ipnet.IpNet) :
    ∃ out, ipnet.ipnet.IpNet.Insts.CoreCmpPartialEqIpNet.eq a b =
      Result.ok out ∧ (out ↔ netKey a = netKey b) := by
  cases a with
  | V4 a =>
    cases b with
    | V4 b =>
      rcases IPv4Derived.eq_spec a b with ⟨out, hout, hiff⟩
      refine ⟨out, ?_, ?_⟩
      · simpa [ipnet.ipnet.IpNet.Insts.CoreCmpPartialEqIpNet.eq,
          ipnet.ipnet.IpNet.read_discriminant] using hout
      · simpa [netKey, IPv4Derived.key] using hiff
    | V6 b =>
      refine ⟨false, ?_, ?_⟩ <;>
        simp [ipnet.ipnet.IpNet.Insts.CoreCmpPartialEqIpNet.eq,
          netKey, ipnet.ipnet.IpNet.read_discriminant]
  | V6 a =>
    cases b with
    | V4 b =>
      refine ⟨false, ?_, ?_⟩ <;>
        simp [ipnet.ipnet.IpNet.Insts.CoreCmpPartialEqIpNet.eq,
          netKey, ipnet.ipnet.IpNet.read_discriminant]
    | V6 b =>
      rcases IPv6Derived.net_eq_spec a b with ⟨out, hout, hiff⟩
      refine ⟨out, ?_, ?_⟩
      · simpa [ipnet.ipnet.IpNet.Insts.CoreCmpPartialEqIpNet.eq,
          ipnet.ipnet.IpNet.read_discriminant] using hout
      · simpa [netKey, IPv6Derived.netKey] using hiff

theorem net_cmp_spec (a b : ipnet.ipnet.IpNet) :
    ipnet.ipnet.IpNet.Insts.CoreCmpOrd.cmp a b =
      Result.ok (netCompare a b) := by
  cases a <;> cases b <;>
    simp [ipnet.ipnet.IpNet.Insts.CoreCmpOrd.cmp,
      ipnet.ipnet.IpNet.read_discriminant, core.cmp.impls.OrdIsize.cmp,
      netCompare, IPv4Derived.cmp_spec, IPv6Derived.net_cmp_spec,
      lift, bind_ok]
  all_goals rfl

theorem net_partial_cmp_spec (a b : ipnet.ipnet.IpNet) :
    ipnet.ipnet.IpNet.Insts.CoreCmpPartialOrdIpNet.partial_cmp a b =
      Result.ok (some (netCompare a b)) := by
  simp [ipnet.ipnet.IpNet.Insts.CoreCmpPartialOrdIpNet.partial_cmp,
    net_cmp_spec, bind_ok]

theorem range_eq_spec (a b : ipnet.ipext.IpAddrRange) :
    ∃ out, ipnet.ipext.IpAddrRange.Insts.CoreCmpPartialEqIpAddrRange.eq a b =
      Result.ok out ∧ (out ↔ rangeKey a = rangeKey b) := by
  cases a with
  | V4 a =>
    cases b with
    | V4 b =>
      rcases IPv4IteratorDerived.range_eq_spec a b with ⟨out, hout, hiff⟩
      refine ⟨out, ?_, ?_⟩
      · simpa [ipnet.ipext.IpAddrRange.Insts.CoreCmpPartialEqIpAddrRange.eq,
          ipnet.ipext.IpAddrRange.read_discriminant] using hout
      · simpa [rangeKey, IPv4IteratorDerived.rangeKey] using hiff
    | V6 b =>
      refine ⟨false, ?_, ?_⟩ <;>
        simp [ipnet.ipext.IpAddrRange.Insts.CoreCmpPartialEqIpAddrRange.eq,
          rangeKey, ipnet.ipext.IpAddrRange.read_discriminant]
  | V6 a =>
    cases b with
    | V4 b =>
      refine ⟨false, ?_, ?_⟩ <;>
        simp [ipnet.ipext.IpAddrRange.Insts.CoreCmpPartialEqIpAddrRange.eq,
          rangeKey, ipnet.ipext.IpAddrRange.read_discriminant]
    | V6 b =>
      rcases IPv6Derived.range_eq_spec a b with ⟨out, hout, hiff⟩
      refine ⟨out, ?_, ?_⟩
      · simpa [ipnet.ipext.IpAddrRange.Insts.CoreCmpPartialEqIpAddrRange.eq,
          ipnet.ipext.IpAddrRange.read_discriminant] using hout
      · simpa [rangeKey, IPv6Derived.rangeKey] using hiff

theorem range_cmp_spec (a b : ipnet.ipext.IpAddrRange) :
    ipnet.ipext.IpAddrRange.Insts.CoreCmpOrd.cmp a b =
      Result.ok (rangeCompare a b) := by
  cases a <;> cases b <;>
    simp [ipnet.ipext.IpAddrRange.Insts.CoreCmpOrd.cmp,
      ipnet.ipext.IpAddrRange.read_discriminant,
      core.cmp.impls.OrdIsize.cmp, rangeCompare,
      IPv4IteratorDerived.range_cmp_spec, IPv6Derived.range_cmp_spec,
      lift, bind_ok]
  all_goals rfl

theorem range_partial_cmp_spec (a b : ipnet.ipext.IpAddrRange) :
    ipnet.ipext.IpAddrRange.Insts.CoreCmpPartialOrdIpAddrRange.partial_cmp a b =
      Result.ok (some (rangeCompare a b)) := by
  simp [ipnet.ipext.IpAddrRange.Insts.CoreCmpPartialOrdIpAddrRange.partial_cmp,
    range_cmp_spec, bind_ok]

theorem subnets_eq_spec (a b : ipnet.ipnet.IpSubnets) :
    ∃ out, ipnet.ipnet.IpSubnets.Insts.CoreCmpPartialEqIpSubnets.eq a b =
      Result.ok out ∧ (out ↔ subnetsKey a = subnetsKey b) := by
  cases a with
  | V4 a =>
    cases b with
    | V4 b =>
      rcases IPv4IteratorDerived.subnets_eq_spec a b with ⟨out, hout, hiff⟩
      refine ⟨out, ?_, ?_⟩
      · simpa [ipnet.ipnet.IpSubnets.Insts.CoreCmpPartialEqIpSubnets.eq,
          ipnet.ipnet.IpSubnets.read_discriminant] using hout
      · simpa [subnetsKey, IPv4IteratorDerived.subnetsKey] using hiff
    | V6 b =>
      refine ⟨false, ?_, ?_⟩ <;>
        simp [ipnet.ipnet.IpSubnets.Insts.CoreCmpPartialEqIpSubnets.eq,
          subnetsKey, ipnet.ipnet.IpSubnets.read_discriminant]
  | V6 a =>
    cases b with
    | V4 b =>
      refine ⟨false, ?_, ?_⟩ <;>
        simp [ipnet.ipnet.IpSubnets.Insts.CoreCmpPartialEqIpSubnets.eq,
          subnetsKey, ipnet.ipnet.IpSubnets.read_discriminant]
    | V6 b =>
      rcases IPv6Derived.subnets_eq_spec a b with ⟨out, hout, hiff⟩
      refine ⟨out, ?_, ?_⟩
      · simpa [ipnet.ipnet.IpSubnets.Insts.CoreCmpPartialEqIpSubnets.eq,
          ipnet.ipnet.IpSubnets.read_discriminant] using hout
      · simpa [subnetsKey, IPv6Derived.subnetsKey] using hiff

theorem subnets_cmp_spec (a b : ipnet.ipnet.IpSubnets) :
    ipnet.ipnet.IpSubnets.Insts.CoreCmpOrd.cmp a b =
      Result.ok (subnetsCompare a b) := by
  cases a <;> cases b <;>
    simp [ipnet.ipnet.IpSubnets.Insts.CoreCmpOrd.cmp,
      ipnet.ipnet.IpSubnets.read_discriminant,
      core.cmp.impls.OrdIsize.cmp, subnetsCompare,
      IPv4IteratorDerived.subnets_cmp_spec, IPv6Derived.subnets_cmp_spec,
      lift, bind_ok]
  all_goals rfl

theorem subnets_partial_cmp_spec (a b : ipnet.ipnet.IpSubnets) :
    ipnet.ipnet.IpSubnets.Insts.CoreCmpPartialOrdIpSubnets.partial_cmp a b =
      Result.ok (some (subnetsCompare a b)) := by
  simp [ipnet.ipnet.IpSubnets.Insts.CoreCmpPartialOrdIpSubnets.partial_cmp,
    subnets_cmp_spec, bind_ok]

end TaggedDerived
