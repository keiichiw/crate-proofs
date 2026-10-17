module
public import Proofs.Arithmetic
public section

open Aeneas Aeneas.Std Result

namespace IPv6BitOps

theorem ipv6_and_addr_spec (a b : ipnet.core.net.ip_addr.Ipv6Addr) :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpBitAndIpv6AddrIpv6Addr.bitand a b =
        Result.ok out ∧
      CidrModel.ipv6Value out = CidrModel.ipv6Value a &&& CidrModel.ipv6Value b := by
  rcases AddressConversions.ipv6_into_u128_spec a with ⟨x, hx, hxv⟩
  rcases AddressConversions.ipv6_into_u128_spec b with ⟨y, hy, hyv⟩
  rcases AddressConversions.ipv6_from_u128_spec (x &&& y) with ⟨out, hout, houtv⟩
  refine ⟨out, ?_, ?_⟩
  · simp [ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpBitAndIpv6AddrIpv6Addr.bitand,
      core.convert.IntoFrom.into, hx, hy, hout, lift, bind_ok]
  · rw [houtv, ipnet.u128_and_value, hxv, hyv]

theorem ipv6_and_u128_spec (a : ipnet.core.net.ip_addr.Ipv6Addr) (b : U128) :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpBitAndU128Ipv6Addr.bitand a b =
        Result.ok out ∧
      CidrModel.ipv6Value out = CidrModel.ipv6Value a &&& b.val := by
  rcases AddressConversions.ipv6_into_u128_spec a with ⟨x, hx, hxv⟩
  rcases AddressConversions.ipv6_from_u128_spec (x &&& b) with ⟨out, hout, houtv⟩
  refine ⟨out, ?_, ?_⟩
  · simp [ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpBitAndU128Ipv6Addr.bitand,
      core.convert.IntoFrom.into, hx, hout, lift, bind_ok]
  · rw [houtv, ipnet.u128_and_value, hxv]

theorem ipv6_or_addr_spec (a b : ipnet.core.net.ip_addr.Ipv6Addr) :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpBitOrIpv6AddrIpv6Addr.bitor a b =
        Result.ok out ∧
      CidrModel.ipv6Value out = CidrModel.ipv6Value a ||| CidrModel.ipv6Value b := by
  rcases AddressConversions.ipv6_into_u128_spec a with ⟨x, hx, hxv⟩
  rcases AddressConversions.ipv6_into_u128_spec b with ⟨y, hy, hyv⟩
  rcases AddressConversions.ipv6_from_u128_spec (x ||| y) with ⟨out, hout, houtv⟩
  refine ⟨out, ?_, ?_⟩
  · simp [ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpBitOrIpv6AddrIpv6Addr.bitor,
      core.convert.IntoFrom.into, hx, hy, hout, lift, bind_ok]
  · rw [houtv, ipnet.u128_or_value, hxv, hyv]

theorem ipv6_or_u128_spec (a : ipnet.core.net.ip_addr.Ipv6Addr) (b : U128) :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpBitOrU128Ipv6Addr.bitor a b =
        Result.ok out ∧
      CidrModel.ipv6Value out = CidrModel.ipv6Value a ||| b.val := by
  rcases AddressConversions.ipv6_into_u128_spec a with ⟨x, hx, hxv⟩
  rcases AddressConversions.ipv6_from_u128_spec (x ||| b) with ⟨out, hout, houtv⟩
  refine ⟨out, ?_, ?_⟩
  · simp [ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpBitOrU128Ipv6Addr.bitor,
      core.convert.IntoFrom.into, hx, hout, lift, bind_ok]
  · rw [houtv, ipnet.u128_or_value, hxv]

end IPv6BitOps
