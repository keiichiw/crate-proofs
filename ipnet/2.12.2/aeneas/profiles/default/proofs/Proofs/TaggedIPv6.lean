module
public import Proofs.IPv6NetOps

public section

namespace TaggedIPv6

open Aeneas Aeneas.Std Result

/-- The actual tagged dispatch retains both endpoints of every valid IPv6
block, including /0 and /128. -/
theorem hosts_v6_spec (n : ipnet.ipnet.Ipv6Net)
    (hp : n.prefix_len.val ≤ 128) :
    ∃ out, ipnet.ipnet.IpNet.hosts (.V6 n) = Result.ok (.V6 out) ∧
      CidrModel.ipv6Value out.start =
        CidrModel.lower 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val ∧
      CidrModel.ipv6Value out.end =
        CidrModel.upper 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val ∧
      IPv6NetOps.remaining out = RangeMath.ofInclusive
        (CidrModel.lower 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val)
        (CidrModel.upper 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val) := by
  rcases IPv6NetOps.hosts_spec n hp with ⟨out, hcall, hstart, hend, hrem⟩
  refine ⟨out, ?_, hstart, hend, hrem⟩
  simp [ipnet.ipnet.IpNet.hosts, hcall]

/-- V6 tagged subnet construction preserves the exact validity check, raw
endpoints, prefix and tag. -/
theorem subnets_v6_spec (n : ipnet.ipnet.Ipv6Net) (q : U8)
    (hp : n.prefix_len.val ≤ 128) :
    ∃ out : core.result.Result ipnet.ipnet.IpSubnets ipnet.ipnet.PrefixLenError,
      ipnet.ipnet.IpNet.subnets (.V6 n) q = Result.ok out ∧
      (if q.val < n.prefix_len.val ∨ 128 < q.val then
         out = .Err ()
       else
         ∃ s, out = .Ok (.V6 s) ∧
           CidrModel.ipv6Value s.start =
             CidrModel.lower 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val ∧
           CidrModel.ipv6Value s.end =
             CidrModel.upper 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val ∧
           s.min_prefix_len = q) := by
  rcases IPv6NetOps.subnets_spec n q hp with ⟨out, hcall, hpost⟩
  by_cases hbad : q.val < n.prefix_len.val ∨ 128 < q.val
  · simp only [hbad, ↓reduceIte] at hpost ⊢
    subst out
    refine ⟨.Err (), ?_, rfl⟩
    simp [ipnet.ipnet.IpNet.subnets, hcall, ipnet.core.result.Result.map]
  · simp only [hbad, ↓reduceIte] at hpost ⊢
    rcases hpost with ⟨s, hout, hs, he, hq⟩
    subst out
    refine ⟨.Ok (.V6 s), ?_, ⟨s, rfl, hs, he, hq⟩⟩
    simp [ipnet.ipnet.IpNet.subnets, hcall, ipnet.core.result.Result.map,
      ipnet.ipnet.IpSubnets.V6.constructor,
      ipnet.P.Insts.CoreOpsFunctionFnOnceTupleIpv6SubnetsIpSubnets.call_once]

/-- Tagged supernet returns no parent only for /0 and otherwise the canonical
immediate /p-1 parent, retaining V6. -/
theorem supernet_v6_spec (n : ipnet.ipnet.Ipv6Net)
    (hp : n.prefix_len.val ≤ 128) :
    ∃ out, ipnet.ipnet.IpNet.supernet (.V6 n) = Result.ok out ∧
      (if n.prefix_len.val = 0 then out = none else
        ∃ parent, out = some (.V6 parent) ∧
          parent.prefix_len.val = n.prefix_len.val - 1 ∧
          CidrModel.ipv6Value parent.addr =
            CidrModel.lower 128 (CidrModel.ipv6Value n.addr)
              (n.prefix_len.val - 1) ∧
          parent.prefix_len.val ≤ 128 ∧
          CidrModel.subset 128 (CidrModel.ipv6Value parent.addr)
            parent.prefix_len.val (CidrModel.ipv6Value n.addr) n.prefix_len.val) := by
  rcases IPv6NetOps.supernet_spec n hp with ⟨out, hcall, hpost⟩
  by_cases hzero : n.prefix_len.val = 0
  · simp only [hzero, ↓reduceIte] at hpost ⊢
    subst out
    refine ⟨none, ?_, rfl⟩
    simp [ipnet.ipnet.IpNet.supernet, hcall, core.option.Option.map]
  · simp only [hzero, ↓reduceIte] at hpost ⊢
    rcases hpost with ⟨parent, hout, hp', hv, hvalid, hsubset⟩
    subst out
    refine ⟨some (.V6 parent), ?_, ⟨parent, rfl, hp', hv, hvalid, hsubset⟩⟩
    simp [ipnet.ipnet.IpNet.supernet, hcall, core.option.Option.map,
      ipnet.ipnet.IpNet.V6.constructor,
      ipnet.P.Insts.CoreOpsFunctionFnOnceTupleIpv6NetIpNet.call_once]

/-- V6 sibling dispatch is exactly the independent same-parent criterion,
including self-comparison. -/
theorem is_sibling_v6_spec (n m : ipnet.ipnet.Ipv6Net)
    (hn : n.prefix_len.val ≤ 128) (hm : m.prefix_len.val ≤ 128) :
    ∃ out, ipnet.ipnet.IpNet.is_sibling (.V6 n) (.V6 m) = Result.ok out ∧
      (out = true ↔
        0 < n.prefix_len.val ∧ n.prefix_len.val = m.prefix_len.val ∧
        CidrModel.lower 128 (CidrModel.ipv6Value n.addr)
          (n.prefix_len.val - 1) =
        CidrModel.lower 128 (CidrModel.ipv6Value m.addr)
          (m.prefix_len.val - 1)) := by
  rcases IPv6NetOps.is_sibling_spec n m hn hm with ⟨out, hcall, hpost⟩
  exact ⟨out, by simpa [ipnet.ipnet.IpNet.is_sibling] using hcall, hpost⟩

end TaggedIPv6
