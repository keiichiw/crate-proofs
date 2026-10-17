module
public import Proofs.IPv4NetOps

public section

namespace TaggedDefaultFrom

open Aeneas Aeneas.Std Result

/-- The full tagged default is IPv4 zero with prefix zero. -/
theorem ipnet_default_spec :
    ∃ n, ipnet.ipnet.IpNet.Insts.CoreDefaultDefault.default =
      Result.ok (.V4 n) ∧
      CidrModel.ipv4Value n.addr = 0 ∧ n.prefix_len = 0#u8 := by
  rcases IPv4NetOps.default_spec with ⟨n, hdefault, haddr, hp⟩
  refine ⟨n, ?_, haddr, hp⟩
  simp [ipnet.ipnet.IpNet.Insts.CoreDefaultDefault.default, hdefault]

/-- The co-selected concrete IPv6 conversion preserves the original address. -/
theorem ipv6_from_addr_spec (a : ipnet.core.net.ip_addr.Ipv6Addr) :
    ipnet.ipnet.Ipv6Net.Insts.CoreConvertFromIpv6Addr.from a =
      Result.ok { addr := a, prefix_len := 128#u8 } := by
  rfl

/-- The full tagged conversion preserves family and all host bits. -/
theorem ipnet_from_addr_spec (a : ipnet.core.net.ip_addr.IpAddr) :
    ipnet.ipnet.IpNet.Insts.CoreConvertFromIpAddr.from a =
      match a with
      | .V4 x => Result.ok (.V4 { addr := x, prefix_len := 32#u8 })
      | .V6 x => Result.ok (.V6 { addr := x, prefix_len := 128#u8 }) := by
  cases a with
  | V4 x =>
    simp [ipnet.ipnet.IpNet.Insts.CoreConvertFromIpAddr.from,
      core.convert.IntoFrom.into, IPv4NetOps.from_ipv4_spec]
  | V6 x =>
    simp [ipnet.ipnet.IpNet.Insts.CoreConvertFromIpAddr.from,
      core.convert.IntoFrom.into, ipv6_from_addr_spec]

end TaggedDefaultFrom
