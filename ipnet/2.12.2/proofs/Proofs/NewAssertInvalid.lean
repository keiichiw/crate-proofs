module
public import Proofs.Core

public section

open Aeneas Aeneas.Std Result

namespace NewAssertInvalid

/-- The assertion fails precisely outside the IPv4 prefix domain. -/
theorem ipv4_invalid (ip : ipnet.core.net.ip_addr.Ipv4Addr) (p : U8)
    (hp : 32 < p.val) :
    ipnet.ipnet.Ipv4Net.new_assert ip p = Result.fail .assertionFailure := by
  simp [ipnet.ipnet.Ipv4Net.new_assert, show ¬ p.val ≤ 32 by omega]

/-- The assertion fails precisely outside the IPv6 prefix domain. -/
theorem ipv6_invalid (ip : ipnet.core.net.ip_addr.Ipv6Addr) (p : U8)
    (hp : 128 < p.val) :
    ipnet.ipnet.Ipv6Net.new_assert ip p = Result.fail .assertionFailure := by
  simp [ipnet.ipnet.Ipv6Net.new_assert, show ¬ p.val ≤ 128 by omega]

/-- Tagged assertion failure dispatches to the prefix bound of its stored family. -/
theorem tagged_invalid (ip : ipnet.core.net.ip_addr.IpAddr) (p : U8)
    (hp : match ip with
      | .V4 _ => 32 < p.val
      | .V6 _ => 128 < p.val) :
    ipnet.ipnet.IpNet.new_assert ip p = Result.fail .assertionFailure := by
  cases ip with
  | V4 a =>
    simp [ipnet.ipnet.IpNet.new_assert, ipv4_invalid a p hp]
  | V6 a =>
    simp [ipnet.ipnet.IpNet.new_assert, ipv6_invalid a p hp]

/-- Full runtime classification for the concrete IPv4 assertion constructor. -/
theorem ipv4_full_spec (ip : ipnet.core.net.ip_addr.Ipv4Addr) (p : U8) :
    ipnet.ipnet.Ipv4Net.new_assert ip p =
      if p.val ≤ 32 then Result.ok { addr := ip, prefix_len := p }
      else Result.fail .assertionFailure := by
  by_cases hp : p.val ≤ 32
  · simp [hp, ipnet.ipnet.Ipv4Net.new_assert]
  · have hgt : 32 < p.val := by omega
    simp [hp, ipv4_invalid ip p hgt]

/-- Full runtime classification for the concrete IPv6 assertion constructor. -/
theorem ipv6_full_spec (ip : ipnet.core.net.ip_addr.Ipv6Addr) (p : U8) :
    ipnet.ipnet.Ipv6Net.new_assert ip p =
      if p.val ≤ 128 then Result.ok { addr := ip, prefix_len := p }
      else Result.fail .assertionFailure := by
  by_cases hp : p.val ≤ 128
  · simp [hp, ipnet.ipnet.Ipv6Net.new_assert]
  · have hgt : 128 < p.val := by omega
    simp [hp, ipv6_invalid ip p hgt]

/-- Tagged dispatch keeps the raw family/address in each valid branch. -/
theorem tagged_full_spec (ip : ipnet.core.net.ip_addr.IpAddr) (p : U8) :
    ipnet.ipnet.IpNet.new_assert ip p =
      match ip with
      | .V4 a =>
          if p.val ≤ 32 then Result.ok (.V4 { addr := a, prefix_len := p })
          else Result.fail .assertionFailure
      | .V6 a =>
          if p.val ≤ 128 then Result.ok (.V6 { addr := a, prefix_len := p })
          else Result.fail .assertionFailure := by
  cases ip with
  | V4 a =>
    by_cases hp : p.val ≤ 32
    · simp [hp, ipnet.ipnet.IpNet.new_assert, ipv4_full_spec]
    · simp [hp, ipnet.ipnet.IpNet.new_assert, ipv4_full_spec]
  | V6 a =>
    by_cases hp : p.val ≤ 128
    · simp [hp, ipnet.ipnet.IpNet.new_assert, ipv6_full_spec]
    · simp [hp, ipnet.ipnet.IpNet.new_assert, ipv6_full_spec]

end NewAssertInvalid
