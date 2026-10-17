module
public import Proofs.IPv4NetOps

public section

namespace TaggedIPv4

open Aeneas Aeneas.Std Result

/-- The selected conversion preserves every raw IPv4 range, including reversed endpoints. -/
theorem from_ipv4_range_spec (r : ipnet.ipext.Ipv4AddrRange) :
    ipnet.ipext.IpAddrRange.Insts.CoreConvertFromIpv4AddrRange.from r =
      Result.ok (.V4 r) := by
  rfl

/-- The selected conversion preserves every raw IPv4 subnet iterator, including invalid q. -/
theorem from_ipv4_subnets_spec (r : ipnet.ipnet.Ipv4Subnets) :
    ipnet.ipnet.IpSubnets.Insts.CoreConvertFromIpv4Subnets.from r =
      Result.ok (.V4 r) := by
  rfl

/-- The co-selected IPv6 conversion also preserves every raw range exactly. -/
theorem from_ipv6_range_spec (r : ipnet.ipext.Ipv6AddrRange) :
    ipnet.ipext.IpAddrRange.Insts.CoreConvertFromIpv6AddrRange.from r =
      Result.ok (.V6 r) := by
  rfl

/-- The co-selected IPv6 conversion preserves every raw iterator state exactly. -/
theorem from_ipv6_subnets_spec (r : ipnet.ipnet.Ipv6Subnets) :
    ipnet.ipnet.IpSubnets.Insts.CoreConvertFromIpv6Subnets.from r =
      Result.ok (.V6 r) := by
  rfl

/-- V4-tagged `hosts` has the exact IPv4 host endpoints and remaining interval. -/
theorem hosts_v4_spec (n : ipnet.ipnet.Ipv4Net)
    (hp : n.prefix_len.val ≤ 32) :
    ∃ out, ipnet.ipnet.IpNet.hosts (.V4 n) = Result.ok (.V4 out) ∧
      CidrModel.ipv4Value out.start =
        IPv4NetMath.hostStart (CidrModel.ipv4Value n.addr) n.prefix_len.val ∧
      CidrModel.ipv4Value out.end =
        IPv4NetMath.hostStop (CidrModel.ipv4Value n.addr) n.prefix_len.val ∧
      RangeNext.remaining out =
        IPv4NetMath.hostsRemaining (CidrModel.ipv4Value n.addr) n.prefix_len.val := by
  rcases IPv4NetOps.hosts_spec n hp with ⟨out, hcall, hstart, hend, hrem⟩
  refine ⟨out, ?_, hstart, hend, hrem⟩
  simp [ipnet.ipnet.IpNet.hosts, hcall]

/-- V4-tagged `subnets` preserves ordinary prefix errors and exact V4 state. -/
theorem subnets_v4_spec (n : ipnet.ipnet.Ipv4Net) (q : U8)
    (hp : n.prefix_len.val ≤ 32) :
    ∃ out : core.result.Result ipnet.ipnet.IpSubnets ipnet.ipnet.PrefixLenError,
      ipnet.ipnet.IpNet.subnets (.V4 n) q = Result.ok out ∧
      (if q.val < n.prefix_len.val ∨ 32 < q.val then
         out = .Err ()
       else
         ∃ s, out = .Ok (.V4 s) ∧
           CidrModel.ipv4Value s.start =
             CidrModel.lower 32 (CidrModel.ipv4Value n.addr) n.prefix_len.val ∧
           CidrModel.ipv4Value s.end =
             CidrModel.upper 32 (CidrModel.ipv4Value n.addr) n.prefix_len.val ∧
           s.min_prefix_len = q) := by
  rcases IPv4NetOps.subnets_spec n q hp with ⟨out, hcall, hpost⟩
  by_cases hbad : q.val < n.prefix_len.val ∨ 32 < q.val
  · simp only [hbad, ↓reduceIte] at hpost ⊢
    subst out
    refine ⟨.Err (), ?_, rfl⟩
    simp [ipnet.ipnet.IpNet.subnets, hcall, ipnet.core.result.Result.map]
  · simp only [hbad, ↓reduceIte] at hpost ⊢
    rcases hpost with ⟨s, hout, hs, he, hq⟩
    subst out
    refine ⟨.Ok (.V4 s), ?_, ⟨s, rfl, hs, he, hq⟩⟩
    simp [ipnet.ipnet.IpNet.subnets, hcall, ipnet.core.result.Result.map,
      ipnet.ipnet.IpSubnets.V4.constructor,
      ipnet.P.Insts.CoreOpsFunctionFnOnceTupleIpv4SubnetsIpSubnets.call_once]

/-- V4-tagged `supernet` returns the canonical parent, or none for /0. -/
theorem supernet_v4_spec (n : ipnet.ipnet.Ipv4Net)
    (hp : n.prefix_len.val ≤ 32) :
    ∃ out, ipnet.ipnet.IpNet.supernet (.V4 n) = Result.ok out ∧
      (if n.prefix_len.val = 0 then out = none else
        ∃ parent, out = some (.V4 parent) ∧
          parent.prefix_len.val = n.prefix_len.val - 1 ∧
          CidrModel.ipv4Value parent.addr =
            CidrModel.lower 32 (CidrModel.ipv4Value n.addr)
              (n.prefix_len.val - 1) ∧
          parent.prefix_len.val ≤ 32 ∧
          CidrModel.subset 32 (CidrModel.ipv4Value parent.addr)
            parent.prefix_len.val (CidrModel.ipv4Value n.addr) n.prefix_len.val) := by
  rcases IPv4NetOps.supernet_spec n hp with ⟨out, hcall, hpost⟩
  by_cases hzero : n.prefix_len.val = 0
  · simp only [hzero, ↓reduceIte] at hpost ⊢
    subst out
    refine ⟨none, ?_, rfl⟩
    simp [ipnet.ipnet.IpNet.supernet, hcall, core.option.Option.map]
  · simp only [hzero, ↓reduceIte] at hpost ⊢
    rcases hpost with ⟨parent, hout, hp', hv, hvalid, hsubset⟩
    subst out
    refine ⟨some (.V4 parent), ?_, ⟨parent, rfl, hp', hv, hvalid, hsubset⟩⟩
    simp [ipnet.ipnet.IpNet.supernet, hcall, core.option.Option.map,
      ipnet.ipnet.IpNet.V4.constructor,
      ipnet.P.Insts.CoreOpsFunctionFnOnceTupleIpv4NetIpNet.call_once]

/-- A V4 pair uses the independent parent-block sibling criterion. -/
theorem is_sibling_v4_spec (n m : ipnet.ipnet.Ipv4Net)
    (hn : n.prefix_len.val ≤ 32) (hm : m.prefix_len.val ≤ 32) :
    ∃ out, ipnet.ipnet.IpNet.is_sibling (.V4 n) (.V4 m) = Result.ok out ∧
      (out = true ↔
        0 < n.prefix_len.val ∧ n.prefix_len.val = m.prefix_len.val ∧
        CidrModel.lower 32 (CidrModel.ipv4Value n.addr)
          (n.prefix_len.val - 1) =
        CidrModel.lower 32 (CidrModel.ipv4Value m.addr)
          (m.prefix_len.val - 1)) := by
  rcases IPv4NetOps.is_sibling_spec n m hn hm with ⟨out, hcall, hpost⟩
  exact ⟨out, by simpa [ipnet.ipnet.IpNet.is_sibling] using hcall, hpost⟩

/-- Mixed sibling tags return false without prefix-validity assumptions. -/
theorem is_sibling_v4_v6_spec (n : ipnet.ipnet.Ipv4Net)
    (m : ipnet.ipnet.Ipv6Net) :
    ipnet.ipnet.IpNet.is_sibling (.V4 n) (.V6 m) = Result.ok false := by
  rfl

theorem is_sibling_v6_v4_spec (n : ipnet.ipnet.Ipv6Net)
    (m : ipnet.ipnet.Ipv4Net) :
    ipnet.ipnet.IpNet.is_sibling (.V6 n) (.V4 m) = Result.ok false := by
  rfl

end TaggedIPv4
