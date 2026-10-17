module
public import Proofs.IPv4SubnetIterator
public import Proofs.IPv4SubnetInvalid
public import Proofs.IPv4SubnetActualTrace

public section

open Aeneas Aeneas.Std Result

namespace IPv4SubnetAll

/-- Complete raw-state classification of the extracted IPv4 subnet iterator.
    Reversed ranges are exhausted for every stored prefix. Live ranges with
    q≤32 yield the exact largest aligned CIDR block and residual state; live
    ranges with q>32 take the modeled Rust unwrap panic path. -/
theorem next_raw_spec (r : ipnet.ipnet.Ipv4Subnets) :
    (CidrModel.ipv4Value r.end < CidrModel.ipv4Value r.start →
      ipnet.ipnet.Ipv4Subnets.Insts.CoreIterTraitsIteratorIteratorIpv4Net.next r =
        Result.ok (none, r) ∧ IPv4SubnetStep.remaining r = .empty) ∧
    (∀ (hse : CidrModel.ipv4Value r.start ≤ CidrModel.ipv4Value r.end)
        (hq : r.min_prefix_len.val ≤ 32),
      ∃ net r',
        ipnet.ipnet.Ipv4Subnets.Insts.CoreIterTraitsIteratorIteratorIpv4Net.next r =
          Result.ok (some net, r') ∧
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
      ipnet.ipnet.Ipv4Subnets.Insts.CoreIterTraitsIteratorIteratorIpv4Net.next r =
        Result.fail .panic) := by
  exact ⟨fun h => IPv4SubnetStep.next_empty_spec r h,
    fun hse hq => IPv4SubnetStep.next_live_spec r hq hse,
    fun hse hq => IPv4SubnetInvalid.next_invalid_live r hse hq⟩

end IPv4SubnetAll
