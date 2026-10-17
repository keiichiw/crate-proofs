module
public import Proofs.IPv6SubnetIterator
public import Proofs.IPv6SubnetInvalid
public import Proofs.IPv6SubnetActualTrace

public section

open Aeneas Aeneas.Std Result

namespace IPv6SubnetAll

/-- Complete raw-state classification of the extracted IPv6 subnet iterator.
    Reversed ranges are exhausted for every stored prefix. Live ranges with
    q≤128 yield the exact largest aligned CIDR block and residual state; live
    ranges with q>128 take the modeled Rust unwrap panic path. -/
theorem next_raw_spec (r : ipnet.ipnet.Ipv6Subnets) :
    (CidrModel.ipv6Value r.end < CidrModel.ipv6Value r.start →
      ipnet.ipnet.Ipv6Subnets.Insts.CoreIterTraitsIteratorIteratorIpv6Net.next r =
        Result.ok (none, r) ∧ IPv6SubnetStep.remaining r = .empty) ∧
    (∀ (hse : CidrModel.ipv6Value r.start ≤ CidrModel.ipv6Value r.end)
        (hq : r.min_prefix_len.val ≤ 128),
      ∃ net r',
        ipnet.ipnet.Ipv6Subnets.Insts.CoreIterTraitsIteratorIteratorIpv6Net.next r =
          Result.ok (some net, r') ∧
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
      ipnet.ipnet.Ipv6Subnets.Insts.CoreIterTraitsIteratorIteratorIpv6Net.next r =
        Result.fail .panic) := by
  exact ⟨fun h => IPv6SubnetStep.next_empty_spec r h,
    fun hse hq => IPv6SubnetStep.next_live_spec r hq hse,
    fun hse hq => IPv6SubnetInvalid.next_invalid_live r hse hq⟩

end IPv6SubnetAll
