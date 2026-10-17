module
public import Proofs.IPv4SubnetAll
public import Proofs.IPv6SubnetAll

public section

open Aeneas Aeneas.Std Result

namespace TaggedSubnets

private theorem map_v4 (o : Option ipnet.ipnet.Ipv4Net) :
    core.option.Option.map ipnet.P.Insts.CoreOpsFunctionFnOnceTupleIpv4NetIpNet o
      ipnet.ipnet.IpNet.V4.constructor = Result.ok (o.map ipnet.ipnet.IpNet.V4) := by
  cases o <;>
    simp [core.option.Option.map,
      ipnet.P.Insts.CoreOpsFunctionFnOnceTupleIpv4NetIpNet.call_once,
      ipnet.ipnet.IpNet.V4.constructor]

private theorem map_v6 (o : Option ipnet.ipnet.Ipv6Net) :
    core.option.Option.map ipnet.P.Insts.CoreOpsFunctionFnOnceTupleIpv6NetIpNet o
      ipnet.ipnet.IpNet.V6.constructor = Result.ok (o.map ipnet.ipnet.IpNet.V6) := by
  cases o <;>
    simp [core.option.Option.map,
      ipnet.P.Insts.CoreOpsFunctionFnOnceTupleIpv6NetIpNet.call_once,
      ipnet.ipnet.IpNet.V6.constructor]

theorem forward_v4_ok (r r' : ipnet.ipnet.Ipv4Subnets) (o : Option ipnet.ipnet.Ipv4Net)
    (h : ipnet.ipnet.Ipv4Subnets.Insts.CoreIterTraitsIteratorIteratorIpv4Net.next r =
      Result.ok (o, r')) :
    ipnet.ipnet.IpSubnets.Insts.CoreIterTraitsIteratorIteratorIpNet.next (.V4 r) =
      Result.ok (o.map ipnet.ipnet.IpNet.V4, .V4 r') := by
  simp [ipnet.ipnet.IpSubnets.Insts.CoreIterTraitsIteratorIteratorIpNet.next,
    h, map_v4]

theorem forward_v6_ok (r r' : ipnet.ipnet.Ipv6Subnets) (o : Option ipnet.ipnet.Ipv6Net)
    (h : ipnet.ipnet.Ipv6Subnets.Insts.CoreIterTraitsIteratorIteratorIpv6Net.next r =
      Result.ok (o, r')) :
    ipnet.ipnet.IpSubnets.Insts.CoreIterTraitsIteratorIteratorIpNet.next (.V6 r) =
      Result.ok (o.map ipnet.ipnet.IpNet.V6, .V6 r') := by
  simp [ipnet.ipnet.IpSubnets.Insts.CoreIterTraitsIteratorIteratorIpNet.next,
    h, map_v6]

theorem forward_v4_panic (r : ipnet.ipnet.Ipv4Subnets)
    (h : ipnet.ipnet.Ipv4Subnets.Insts.CoreIterTraitsIteratorIteratorIpv4Net.next r =
      Result.fail .panic) :
    ipnet.ipnet.IpSubnets.Insts.CoreIterTraitsIteratorIteratorIpNet.next (.V4 r) =
      Result.fail .panic := by
  simp [ipnet.ipnet.IpSubnets.Insts.CoreIterTraitsIteratorIteratorIpNet.next, h]

theorem forward_v6_panic (r : ipnet.ipnet.Ipv6Subnets)
    (h : ipnet.ipnet.Ipv6Subnets.Insts.CoreIterTraitsIteratorIteratorIpv6Net.next r =
      Result.fail .panic) :
    ipnet.ipnet.IpSubnets.Insts.CoreIterTraitsIteratorIteratorIpNet.next (.V6 r) =
      Result.fail .panic := by
  simp [ipnet.ipnet.IpSubnets.Insts.CoreIterTraitsIteratorIteratorIpNet.next, h]

/-- The actual tagged iterator forwards every IPv4 raw-state outcome and
    preserves the concrete updated state inside its tag. -/
theorem next_v4_raw_spec (r : ipnet.ipnet.Ipv4Subnets) :
    (CidrModel.ipv4Value r.end < CidrModel.ipv4Value r.start →
      ipnet.ipnet.IpSubnets.Insts.CoreIterTraitsIteratorIteratorIpNet.next (.V4 r) =
        Result.ok (none, .V4 r) ∧ IPv4SubnetStep.remaining r = .empty) ∧
    (∀ (hse : CidrModel.ipv4Value r.start ≤ CidrModel.ipv4Value r.end)
        (hq : r.min_prefix_len.val ≤ 32),
      ∃ net r',
        ipnet.ipnet.IpSubnets.Insts.CoreIterTraitsIteratorIteratorIpNet.next (.V4 r) =
          Result.ok (some (.V4 net), .V4 r') ∧
        CidrModel.ipv4Value net.addr = CidrModel.ipv4Value r.start ∧
        net.prefix_len.val =
          IPv4SubnetMath.bestPrefix (CidrModel.ipv4Value r.start)
            (CidrModel.ipv4Value r.end + 1) r.min_prefix_len.val hq (by omega) ∧
        IPv4SubnetStep.remaining r' =
          IPv4SubnetMath.residual (CidrModel.ipv4Value r.start)
            (CidrModel.ipv4Value r.end + 1) r.min_prefix_len.val hq (by omega) ∧
        r'.min_prefix_len = r.min_prefix_len) ∧
    (CidrModel.ipv4Value r.start ≤ CidrModel.ipv4Value r.end →
      32 < r.min_prefix_len.val →
      ipnet.ipnet.IpSubnets.Insts.CoreIterTraitsIteratorIteratorIpNet.next (.V4 r) =
        Result.fail .panic) := by
  rcases IPv4SubnetAll.next_raw_spec r with ⟨hempty, hlive, hbad⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h
    obtain ⟨hn, hr⟩ := hempty h
    exact ⟨forward_v4_ok r r none hn, hr⟩
  · intro hse hq
    obtain ⟨net, r', hn, ha, hp, hr, hq'⟩ := hlive hse hq
    exact ⟨net, r', forward_v4_ok r r' (some net) hn, ha, hp, hr, hq'⟩
  · intro hse hq
    exact forward_v4_panic r (hbad hse hq)

/-- The same exact forwarding statement for every IPv6 raw state, including
    the invalid live-prefix panic outcome. -/
theorem next_v6_raw_spec (r : ipnet.ipnet.Ipv6Subnets) :
    (CidrModel.ipv6Value r.end < CidrModel.ipv6Value r.start →
      ipnet.ipnet.IpSubnets.Insts.CoreIterTraitsIteratorIteratorIpNet.next (.V6 r) =
        Result.ok (none, .V6 r) ∧ IPv6SubnetStep.remaining r = .empty) ∧
    (∀ (hse : CidrModel.ipv6Value r.start ≤ CidrModel.ipv6Value r.end)
        (hq : r.min_prefix_len.val ≤ 128),
      ∃ net r',
        ipnet.ipnet.IpSubnets.Insts.CoreIterTraitsIteratorIteratorIpNet.next (.V6 r) =
          Result.ok (some (.V6 net), .V6 r') ∧
        CidrModel.ipv6Value net.addr = CidrModel.ipv6Value r.start ∧
        net.prefix_len.val =
          IPv6SubnetMath.bestPrefix (CidrModel.ipv6Value r.start)
            (CidrModel.ipv6Value r.end + 1) r.min_prefix_len.val hq (by omega) ∧
        IPv6SubnetStep.remaining r' =
          IPv6SubnetMath.residual (CidrModel.ipv6Value r.start)
            (CidrModel.ipv6Value r.end + 1) r.min_prefix_len.val hq (by omega) ∧
        r'.min_prefix_len = r.min_prefix_len) ∧
    (CidrModel.ipv6Value r.start ≤ CidrModel.ipv6Value r.end →
      128 < r.min_prefix_len.val →
      ipnet.ipnet.IpSubnets.Insts.CoreIterTraitsIteratorIteratorIpNet.next (.V6 r) =
        Result.fail .panic) := by
  rcases IPv6SubnetAll.next_raw_spec r with ⟨hempty, hlive, hbad⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h
    obtain ⟨hn, hr⟩ := hempty h
    exact ⟨forward_v6_ok r r none hn, hr⟩
  · intro hse hq
    obtain ⟨net, r', hn, ha, hp, hr, hq'⟩ := hlive hse hq
    exact ⟨net, r', forward_v6_ok r r' (some net) hn, ha, hp, hr, hq'⟩
  · intro hse hq
    exact forward_v6_panic r (hbad hse hq)

/-- One public tagged API, with exhaustive V4 and V6 raw-state contracts. -/
theorem next_raw_spec (r : ipnet.ipnet.IpSubnets) :
    match r with
    | .V4 a =>
      (CidrModel.ipv4Value a.end < CidrModel.ipv4Value a.start →
        ipnet.ipnet.IpSubnets.Insts.CoreIterTraitsIteratorIteratorIpNet.next (.V4 a) =
          Result.ok (none, .V4 a) ∧ IPv4SubnetStep.remaining a = .empty) ∧
      (∀ (hse : CidrModel.ipv4Value a.start ≤ CidrModel.ipv4Value a.end)
          (hq : a.min_prefix_len.val ≤ 32),
        ∃ net a',
          ipnet.ipnet.IpSubnets.Insts.CoreIterTraitsIteratorIteratorIpNet.next (.V4 a) =
            Result.ok (some (.V4 net), .V4 a') ∧
          CidrModel.ipv4Value net.addr = CidrModel.ipv4Value a.start ∧
          net.prefix_len.val = IPv4SubnetMath.bestPrefix
            (CidrModel.ipv4Value a.start) (CidrModel.ipv4Value a.end + 1)
            a.min_prefix_len.val hq (by omega) ∧
          IPv4SubnetStep.remaining a' = IPv4SubnetMath.residual
            (CidrModel.ipv4Value a.start) (CidrModel.ipv4Value a.end + 1)
            a.min_prefix_len.val hq (by omega) ∧
          a'.min_prefix_len = a.min_prefix_len) ∧
      (CidrModel.ipv4Value a.start ≤ CidrModel.ipv4Value a.end →
        32 < a.min_prefix_len.val →
        ipnet.ipnet.IpSubnets.Insts.CoreIterTraitsIteratorIteratorIpNet.next (.V4 a) =
          Result.fail .panic)
    | .V6 a =>
      (CidrModel.ipv6Value a.end < CidrModel.ipv6Value a.start →
        ipnet.ipnet.IpSubnets.Insts.CoreIterTraitsIteratorIteratorIpNet.next (.V6 a) =
          Result.ok (none, .V6 a) ∧ IPv6SubnetStep.remaining a = .empty) ∧
      (∀ (hse : CidrModel.ipv6Value a.start ≤ CidrModel.ipv6Value a.end)
          (hq : a.min_prefix_len.val ≤ 128),
        ∃ net a',
          ipnet.ipnet.IpSubnets.Insts.CoreIterTraitsIteratorIteratorIpNet.next (.V6 a) =
            Result.ok (some (.V6 net), .V6 a') ∧
          CidrModel.ipv6Value net.addr = CidrModel.ipv6Value a.start ∧
          net.prefix_len.val = IPv6SubnetMath.bestPrefix
            (CidrModel.ipv6Value a.start) (CidrModel.ipv6Value a.end + 1)
            a.min_prefix_len.val hq (by omega) ∧
          IPv6SubnetStep.remaining a' = IPv6SubnetMath.residual
            (CidrModel.ipv6Value a.start) (CidrModel.ipv6Value a.end + 1)
            a.min_prefix_len.val hq (by omega) ∧
          a'.min_prefix_len = a.min_prefix_len) ∧
      (CidrModel.ipv6Value a.start ≤ CidrModel.ipv6Value a.end →
        128 < a.min_prefix_len.val →
        ipnet.ipnet.IpSubnets.Insts.CoreIterTraitsIteratorIteratorIpNet.next (.V6 a) =
          Result.fail .panic) := by
  cases r with
  | V4 a => exact next_v4_raw_spec a
  | V6 a => exact next_v6_raw_spec a

end TaggedSubnets
