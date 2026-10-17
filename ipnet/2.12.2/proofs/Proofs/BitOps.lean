module
public import Proofs.Arithmetic
public section

open Aeneas Aeneas.Std Result

namespace BitOps

theorem ipv4_and_addr_spec (a b : ipnet.core.net.ip_addr.Ipv4Addr) :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpBitAndIpv4AddrIpv4Addr.bitand a b =
        Result.ok out ∧
      CidrModel.ipv4Value out = CidrModel.ipv4Value a &&& CidrModel.ipv4Value b := by
  rcases AddressConversions.ipv4_into_u32_spec a with ⟨x, hx, hxv⟩
  rcases AddressConversions.ipv4_into_u32_spec b with ⟨y, hy, hyv⟩
  rcases AddressConversions.ipv4_from_u32_spec (x &&& y) with ⟨out, hout, houtv⟩
  refine ⟨out, ?_, ?_⟩
  · simp [ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpBitAndIpv4AddrIpv4Addr.bitand,
      core.convert.IntoFrom.into, hx, hy, hout, lift, bind_ok]
  · rw [houtv, ipnet.u32_and_value, hxv, hyv]

theorem ipv4_and_u32_spec (a : ipnet.core.net.ip_addr.Ipv4Addr) (b : U32) :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpBitAndU32Ipv4Addr.bitand a b =
        Result.ok out ∧
      CidrModel.ipv4Value out = CidrModel.ipv4Value a &&& b.val := by
  rcases AddressConversions.ipv4_into_u32_spec a with ⟨x, hx, hxv⟩
  rcases AddressConversions.ipv4_from_u32_spec (x &&& b) with ⟨out, hout, houtv⟩
  refine ⟨out, ?_, ?_⟩
  · simp [ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpBitAndU32Ipv4Addr.bitand,
      core.convert.IntoFrom.into, hx, hout, lift, bind_ok]
  · rw [houtv, ipnet.u32_and_value, hxv]

theorem ipv4_or_addr_spec (a b : ipnet.core.net.ip_addr.Ipv4Addr) :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpBitOrIpv4AddrIpv4Addr.bitor a b =
        Result.ok out ∧
      CidrModel.ipv4Value out = CidrModel.ipv4Value a ||| CidrModel.ipv4Value b := by
  rcases AddressConversions.ipv4_into_u32_spec a with ⟨x, hx, hxv⟩
  rcases AddressConversions.ipv4_into_u32_spec b with ⟨y, hy, hyv⟩
  rcases AddressConversions.ipv4_from_u32_spec (x ||| y) with ⟨out, hout, houtv⟩
  refine ⟨out, ?_, ?_⟩
  · simp [ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpBitOrIpv4AddrIpv4Addr.bitor,
      core.convert.IntoFrom.into, hx, hy, hout, lift, bind_ok]
  · rw [houtv, ipnet.u32_or_value, hxv, hyv]

theorem ipv4_or_u32_spec (a : ipnet.core.net.ip_addr.Ipv4Addr) (b : U32) :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpBitOrU32Ipv4Addr.bitor a b =
        Result.ok out ∧
      CidrModel.ipv4Value out = CidrModel.ipv4Value a ||| b.val := by
  rcases AddressConversions.ipv4_into_u32_spec a with ⟨x, hx, hxv⟩
  rcases AddressConversions.ipv4_from_u32_spec (x ||| b) with ⟨out, hout, houtv⟩
  refine ⟨out, ?_, ?_⟩
  · simp [ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpBitOrU32Ipv4Addr.bitor,
      core.convert.IntoFrom.into, hx, hout, lift, bind_ok]
  · rw [houtv, ipnet.u32_or_value, hxv]

end BitOps
