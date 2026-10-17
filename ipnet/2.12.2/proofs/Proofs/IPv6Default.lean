module
public import Proofs.AddressConversions

public section

namespace IPv6Default

open Aeneas Aeneas.Std Result

/-- The selected concrete IPv6 default is the canonical all-space network. -/
theorem default_spec :
    ∃ n,
      ipnet.ipnet.Ipv6Net.Insts.CoreDefaultDefault.default = Result.ok n ∧
      CidrModel.ipv6Value n.addr = 0 ∧ n.prefix_len = 0#u8 := by
  rcases AddressConversions.ipv6_from_u128_spec 0#u128 with ⟨a, ha, hav⟩
  refine ⟨{ addr := a, prefix_len := 0#u8 }, ?_, ?_, rfl⟩
  · simp [ipnet.ipnet.Ipv6Net.Insts.CoreDefaultDefault.default, ha]
  · simpa using hav

end IPv6Default
