module
public import Ipnet

public section

open Aeneas Aeneas.Std

namespace ipnet
set_option linter.dupNamespace false

/-- The raw range constructor stores both IPv4 endpoints exactly, even if reversed. -/
theorem ipv4_range_new_spec (start stop : core.net.ip_addr.Ipv4Addr) :
    ∃ out, ipext.Ipv4AddrRange.new start stop = Result.ok out ∧
      out = { start := start, «end» := stop } := by
  exact ⟨{ start := start, «end» := stop }, rfl, rfl⟩

/-- The raw range constructor stores both IPv6 endpoints exactly, even if reversed. -/
theorem ipv6_range_new_spec (start stop : core.net.ip_addr.Ipv6Addr) :
    ∃ out, ipext.Ipv6AddrRange.new start stop = Result.ok out ∧
      out = { start := start, «end» := stop } := by
  exact ⟨{ start := start, «end» := stop }, rfl, rfl⟩

namespace ipnet

/-- The raw IPv4 subnet iterator constructor stores both endpoints and every
min-prefix byte. No validity claim is made about subsequent iteration. -/
theorem ipv4_subnets_new_spec (start stop : core.net.ip_addr.Ipv4Addr) (p : U8) :
    ∃ out, Ipv4Subnets.new start stop p = Result.ok out ∧
      out = { start := start, «end» := stop, min_prefix_len := p } := by
  exact ⟨{ start := start, «end» := stop, min_prefix_len := p }, rfl, rfl⟩

/-- The raw IPv6 subnet iterator constructor has the same exact storage
behavior for arbitrary endpoints and prefix bytes. -/
theorem ipv6_subnets_new_spec (start stop : core.net.ip_addr.Ipv6Addr) (p : U8) :
    ∃ out, Ipv6Subnets.new start stop p = Result.ok out ∧
      out = { start := start, «end» := stop, min_prefix_len := p } := by
  exact ⟨{ start := start, «end» := stop, min_prefix_len := p }, rfl, rfl⟩

end ipnet
end ipnet
