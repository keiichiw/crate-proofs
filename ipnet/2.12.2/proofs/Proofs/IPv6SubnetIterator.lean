module
public import Proofs.IPv6SubnetStep
public import Proofs.IPv6SubnetStateMath

public section

open Aeneas Aeneas.Std Result
namespace IPv6SubnetStep

/-- Every live valid raw subnet iterator step succeeds, yields the largest
    aligned CIDR block, and stores exactly the independent residual interval. -/
theorem next_live_spec (r : ipnet.ipnet.Ipv6Subnets)
    (hq : r.min_prefix_len.val ≤ 128)
    (hse : CidrModel.ipv6Value r.start ≤ CidrModel.ipv6Value r.end) :
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
      r'.min_prefix_len = r.min_prefix_len := by
  let s := CidrModel.ipv6Value r.start
  let e := CidrModel.ipv6Value r.end
  have heBound : e < 2^128 := CidrModel.ipv6Value_bound r.end
  rcases next_ipv6_subnet_live_spec r.start r.end r.min_prefix_len hse hq with
    ⟨net,hnet,haddr,hprefix⟩
  have hpBound : net.prefix_len.val ≤ 128 := by
    rw [hprefix]
    exact (IPv6SubnetMath.best_bounds s (e+1) r.min_prefix_len.val hq (by omega)).2
  rcases ipnet.ipv6_broadcast_nat_spec net hpBound with ⟨br,hbr,hbrv⟩
  rcases IPv6RangeSteps.ipv6_saturating_add_spec br 1#u128 with ⟨next,hnext,hnextv⟩
  rcases IPv6AddressEq.ipv6_eq_value next br with ⟨same,hsame,hsamev⟩
  let b := IPv6SubnetMath.blockSize s (e+1) r.min_prefix_len.val hq (by omega)
  have hcanon := IPv6SubnetMath.block_canonical s (e+1) r.min_prefix_len.val hq (by omega)
  have hfit := IPv6SubnetMath.block_fits s (e+1) r.min_prefix_len.val hq (by omega)
  have hbPos := IPv6SubnetMath.blockSize_pos s (e+1) r.min_prefix_len.val hq (by omega)
  have hbrEq : CidrModel.ipv6Value br + 1 = s + b := by
    rw [hbrv, haddr, hprefix]
    exact hcanon.2
  have hnextEq : CidrModel.ipv6Value next =
      min (CidrModel.ipv6Value br + 1) (2^128-1) := by
    simpa using hnextv
  have hsameEq : same ↔ CidrModel.ipv6Value next = CidrModel.ipv6Value br := hsamev
  have hbrBound : CidrModel.ipv6Value br < 2^128 := CidrModel.ipv6Value_bound br
  have heLimit : e < IPv6RangeMath.limit := by simpa [IPv6RangeMath.limit] using heBound
  have hfit' : s + b ≤ e + 1 := by simpa [b] using hfit
  have hbPos' : 0 < b := by simpa [b] using hbPos
  have hnextMin : CidrModel.ipv6Value next =
      min (CidrModel.ipv6Value br + 1) IPv6RangeMath.maxAddress := by
    simpa [IPv6RangeMath.maxAddress, IPv6RangeMath.limit] using hnextEq
  have hresidual :
      IPv6SubnetStateMath.residualBlock s e b =
        IPv6SubnetMath.residual s (e+1) r.min_prefix_len.val hq (by omega) := by
    exact IPv6SubnetStateMath.residualBlock_eq_selected s e r.min_prefix_len.val b
      hq hse rfl
  by_cases hlt : s < e
  · have hc : compare s e = Ordering.lt := Nat.compare_eq_lt.mpr hlt
    have hc' : compare (CidrModel.ipv6Value r.start)
        (CidrModel.ipv6Value r.end) = Ordering.lt := hc
    by_cases hb : same
    · rcases IPv6RangeSteps.ipv6_replace_zero_spec r.end with ⟨zero,hzero,hzerov⟩
      have hsat : CidrModel.ipv6Value next = CidrModel.ipv6Value br := hsameEq.mp hb
      have hstate := IPv6SubnetStateMath.saturated_residual_empty s e b
        (CidrModel.ipv6Value br) (CidrModel.ipv6Value next)
        hse heLimit hbPos' hfit' hbrEq hnextMin hsat
      refine ⟨net, { r with start := next, «end» := zero }, ?_, ?_,
        hprefix, ?_, rfl⟩
      · simp [ipnet.ipnet.Ipv6Subnets.Insts.CoreIterTraitsIteratorIteratorIpv6Net.next,
          Comparisons.ipv6_partial_cmp_spec, hc', hnet, hbr, hnext, hsame, hb,
          hzero]
      · simpa [s] using congrArg CidrModel.ipv6Value haddr
      · simp only [remaining, hzerov]
        rw [← hresidual, hstate.1]
        exact hstate.2
    · have hunsat : CidrModel.ipv6Value next ≠ CidrModel.ipv6Value br := by
        intro heq
        exact hb (hsameEq.mpr heq)
      have hstate := IPv6SubnetStateMath.unsaturated_residual s e b
        (CidrModel.ipv6Value br) (CidrModel.ipv6Value next)
        hse heLimit hbPos' hfit' hbrEq hnextMin hunsat
      refine ⟨net, { r with start := next }, ?_, ?_, hprefix, ?_, rfl⟩
      · simp [ipnet.ipnet.Ipv6Subnets.Insts.CoreIterTraitsIteratorIteratorIpv6Net.next,
          Comparisons.ipv6_partial_cmp_spec, hc', hnet, hbr, hnext, hsame, hb]
      · simpa [s] using congrArg CidrModel.ipv6Value haddr
      · simp only [IPv6SubnetStep.remaining]
        rw [← hresidual]
        exact hstate
  · have heq : s = e := by omega
    have hc : compare s e = Ordering.eq := Nat.compare_eq_eq.mpr heq
    have hc' : compare (CidrModel.ipv6Value r.start)
        (CidrModel.ipv6Value r.end) = Ordering.eq := hc
    rcases IPv6RangeSteps.ipv6_replace_zero_spec r.end with ⟨zero,hzero,hzerov⟩
    have hstate := IPv6SubnetStateMath.singleton_residual_empty s b
      (CidrModel.ipv6Value br) (CidrModel.ipv6Value next)
      (by omega : s < IPv6RangeMath.limit) hbPos'
      (by simpa [heq] using hfit') hbrEq hnextMin
    refine ⟨net, { r with start := next, «end» := zero }, ?_, ?_,
      hprefix, ?_, rfl⟩
    · simp [ipnet.ipnet.Ipv6Subnets.Insts.CoreIterTraitsIteratorIteratorIpv6Net.next,
        Comparisons.ipv6_partial_cmp_spec, hc', hnet, hbr, hnext,
        hzero]
    · simpa [s] using congrArg CidrModel.ipv6Value haddr
    · simp only [remaining, hzerov]
      rw [← hresidual, ← heq, hstate.1]
      exact hstate.2

end IPv6SubnetStep
