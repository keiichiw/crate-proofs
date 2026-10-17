module
public import Ipnet

public section

open Aeneas Aeneas.Std

namespace ipnet.ipnet
set_option linter.dupNamespace false

/-- Every IPv4 constructor call terminates normally. Valid prefixes preserve the
original address, including host bits; invalid prefixes produce the Rust error. -/
theorem ipv4_new_spec (ip : core.net.ip_addr.Ipv4Addr) (p : U8) :
    ∃ out : core.result.Result Ipv4Net PrefixLenError,
      Ipv4Net.new ip p = Result.ok out ∧
      out = (if p.val ≤ 32 then core.result.Result.Ok { addr := ip, prefix_len := p }
             else core.result.Result.Err ()) := by
  by_cases hp : p.val ≤ 32
  · refine ⟨core.result.Result.Ok { addr := ip, prefix_len := p }, ?_, ?_⟩
    · simp [Ipv4Net.new, hp]
    · simp [hp]
  · refine ⟨core.result.Result.Err (), ?_, ?_⟩
    · simp [Ipv4Net.new, hp]
    · simp [hp]

/-- IPv6 has the same exact constructor behavior at width 128. -/
theorem ipv6_new_spec (ip : core.net.ip_addr.Ipv6Addr) (p : U8) :
    ∃ out : core.result.Result Ipv6Net PrefixLenError,
      Ipv6Net.new ip p = Result.ok out ∧
      out = (if p.val ≤ 128 then core.result.Result.Ok { addr := ip, prefix_len := p }
             else core.result.Result.Err ()) := by
  by_cases hp : p.val ≤ 128
  · refine ⟨core.result.Result.Ok { addr := ip, prefix_len := p }, ?_, ?_⟩
    · simp [Ipv6Net.new, hp]
    · simp [hp]
  · refine ⟨core.result.Result.Err (), ?_, ?_⟩
    · simp [Ipv6Net.new, hp]
    · simp [hp]

theorem ipv4_addr_spec (n : Ipv4Net) :
    ∃ out, Ipv4Net.impl.addr n = Result.ok out ∧ out = n.addr := by
  exact ⟨n.addr, rfl, rfl⟩

theorem ipv4_prefix_len_spec (n : Ipv4Net) :
    ∃ out, Ipv4Net.impl.prefix_len n = Result.ok out ∧ out = n.prefix_len := by
  exact ⟨n.prefix_len, rfl, rfl⟩

theorem ipv4_max_prefix_len_spec (n : Ipv4Net) :
    ∃ out, Ipv4Net.max_prefix_len n = Result.ok out ∧ out = 32#u8 := by
  exact ⟨32#u8, rfl, rfl⟩

theorem ipv6_addr_spec (n : Ipv6Net) :
    ∃ out, Ipv6Net.impl.addr n = Result.ok out ∧ out = n.addr := by
  exact ⟨n.addr, rfl, rfl⟩

theorem ipv6_prefix_len_spec (n : Ipv6Net) :
    ∃ out, Ipv6Net.impl.prefix_len n = Result.ok out ∧ out = n.prefix_len := by
  exact ⟨n.prefix_len, rfl, rfl⟩

theorem ipv6_max_prefix_len_spec (n : Ipv6Net) :
    ∃ out, Ipv6Net.max_prefix_len n = Result.ok out ∧ out = 128#u8 := by
  exact ⟨128#u8, rfl, rfl⟩


/-- Valid raw IPv4 prefixes satisfy the checked constructor assertion. -/
theorem ipv4_new_assert_spec (ip : core.net.ip_addr.Ipv4Addr) (p : U8)
    (hp : p.val ≤ 32) :
    ∃ out, Ipv4Net.new_assert ip p = Result.ok out ∧
      out = { addr := ip, prefix_len := p } := by
  refine ⟨{ addr := ip, prefix_len := p }, ?_, rfl⟩
  simp [Ipv4Net.new_assert, hp]

theorem ipv6_new_assert_spec (ip : core.net.ip_addr.Ipv6Addr) (p : U8)
    (hp : p.val ≤ 128) :
    ∃ out, Ipv6Net.new_assert ip p = Result.ok out ∧
      out = { addr := ip, prefix_len := p } := by
  refine ⟨{ addr := ip, prefix_len := p }, ?_, rfl⟩
  simp [Ipv6Net.new_assert, hp]

@[expose] def ipNewExpected (ip : core.net.ip_addr.IpAddr) (p : U8) :
    core.result.Result IpNet PrefixLenError :=
  match ip with
  | .V4 a => if p.val ≤ 32 then .Ok (.V4 { addr := a, prefix_len := p }) else .Err ()
  | .V6 a => if p.val ≤ 128 then .Ok (.V6 { addr := a, prefix_len := p }) else .Err ()

/-- Tagged dispatch preserves its family and exact original address. -/
theorem ip_new_spec (ip : core.net.ip_addr.IpAddr) (p : U8) :
    ∃ out, IpNet.new ip p = Result.ok out ∧ out = ipNewExpected ip p := by
  cases ip with
  | V4 a =>
    by_cases hp : p.val ≤ 32
    · have hgt : ¬ 32 < p.val := by omega
      refine ⟨core.result.Result.Ok (.V4 { addr := a, prefix_len := p }), ?_, ?_⟩
      · simp [IpNet.new, Ipv4Net.new, hgt, core.result.Result.Insts.CoreOpsTry.branch, core.convert.IntoFrom.into, IpNet.Insts.CoreConvertFromIpv4Net.from, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · simp [ipNewExpected, hp]
    · have hgt : 32 < p.val := by omega
      refine ⟨core.result.Result.Err (), ?_, ?_⟩
      · simp [IpNet.new, Ipv4Net.new, hgt, core.result.Result.Insts.CoreOpsTry.branch, core.convert.IntoFrom.into, IpNet.Insts.CoreConvertFromIpv4Net.from, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · simp [ipNewExpected, hp]
  | V6 a =>
    by_cases hp : p.val ≤ 128
    · have hgt : ¬ 128 < p.val := by omega
      refine ⟨core.result.Result.Ok (.V6 { addr := a, prefix_len := p }), ?_, ?_⟩
      · simp [IpNet.new, Ipv6Net.new, hgt, core.result.Result.Insts.CoreOpsTry.branch, core.convert.IntoFrom.into, IpNet.Insts.CoreConvertFromIpv6Net.from, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · simp [ipNewExpected, hp]
    · have hgt : 128 < p.val := by omega
      refine ⟨core.result.Result.Err (), ?_, ?_⟩
      · simp [IpNet.new, Ipv6Net.new, hgt, core.result.Result.Insts.CoreOpsTry.branch, core.convert.IntoFrom.into, IpNet.Insts.CoreConvertFromIpv6Net.from, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · simp [ipNewExpected, hp]

theorem ip_new_assert_spec (ip : core.net.ip_addr.IpAddr) (p : U8)
    (hp : match ip with
      | .V4 _ => p.val ≤ 32
      | .V6 _ => p.val ≤ 128) :
    ∃ out, IpNet.new_assert ip p = Result.ok out ∧
      out = match ip with
        | .V4 a => .V4 { addr := a, prefix_len := p }
        | .V6 a => .V6 { addr := a, prefix_len := p } := by
  cases ip with
  | V4 a =>
    refine ⟨_, ?_, rfl⟩
    simp [IpNet.new_assert, Ipv4Net.new_assert, hp]
  | V6 a =>
    refine ⟨_, ?_, rfl⟩
    simp [IpNet.new_assert, Ipv6Net.new_assert, hp]

theorem ip_addr_spec (n : IpNet) :
    ∃ out, IpNet.addr n = Result.ok out ∧
      out = match n with
        | .V4 x => core.net.ip_addr.IpAddr.V4 x.addr
        | .V6 x => core.net.ip_addr.IpAddr.V6 x.addr := by
  cases n <;> exact ⟨_, rfl, rfl⟩

theorem ip_prefix_len_spec (n : IpNet) :
    ∃ out, IpNet.prefix_len n = Result.ok out ∧
      out = match n with
        | .V4 x => x.prefix_len
        | .V6 x => x.prefix_len := by
  cases n <;> exact ⟨_, rfl, rfl⟩

theorem ip_max_prefix_len_spec (n : IpNet) :
    ∃ out, IpNet.max_prefix_len n = Result.ok out ∧
      out = match n with
        | .V4 _ => 32#u8
        | .V6 _ => 128#u8 := by
  cases n <;> exact ⟨_, rfl, rfl⟩

/-- The public IPv4-to-generic conversion preserves the entire network,
including any stored host bits. -/
theorem from_ipv4_spec (n : Ipv4Net) :
    ∃ out, IpNet.Insts.CoreConvertFromIpv4Net.from n = Result.ok out ∧
      out = IpNet.V4 n := by
  exact ⟨IpNet.V4 n, rfl, rfl⟩

/-- The public IPv6-to-generic conversion preserves the entire network. -/
theorem from_ipv6_spec (n : Ipv6Net) :
    ∃ out, IpNet.Insts.CoreConvertFromIpv6Net.from n = Result.ok out ∧
      out = IpNet.V6 n := by
  exact ⟨IpNet.V6 n, rfl, rfl⟩

end ipnet.ipnet
