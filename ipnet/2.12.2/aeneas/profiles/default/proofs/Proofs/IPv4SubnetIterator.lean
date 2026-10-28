module
public import Proofs.IPv4SubnetEquality
public import Proofs.IPv4SubnetStateMath

public section

open Aeneas Aeneas.Std Result
namespace IPv4SubnetStep

/-- Every live valid raw subnet iterator step succeeds, yields the largest
    aligned CIDR block, and stores exactly the independent residual interval. -/
theorem next_live_spec (r : ipnet.ipnet.Ipv4Subnets)
    (hq : r.min_prefix_len.val ≤ 32)
    (hse : CidrModel.ipv4Value r.start ≤ CidrModel.ipv4Value r.end) :
    ∃ net r',
      ipnet.ipnet.Ipv4Subnets.Insts.CoreIterTraitsIteratorIteratorIpv4Net.next r =
        Result.ok (some net, r') ∧
      CidrModel.ipv4Value net.addr = CidrModel.ipv4Value r.start ∧
      net.prefix_len.val =
        IPv4SubnetMath.bestPrefix (CidrModel.ipv4Value r.start)
          (CidrModel.ipv4Value r.end + 1) r.min_prefix_len.val hq (by omega) ∧
      remaining r' =
        IPv4SubnetMath.residual (CidrModel.ipv4Value r.start)
          (CidrModel.ipv4Value r.end + 1) r.min_prefix_len.val hq (by omega) ∧
      r'.min_prefix_len = r.min_prefix_len := by
  let s := CidrModel.ipv4Value r.start
  let e := CidrModel.ipv4Value r.end
  have heBound : e < 2^32 := CidrModel.ipv4Value_bound r.end
  rcases next_ipv4_subnet_live_spec r.start r.end r.min_prefix_len hse hq with
    ⟨net,hnet,haddr,hprefix⟩
  have hpBound : net.prefix_len.val ≤ 32 := by
    rw [hprefix]
    exact (IPv4SubnetMath.best_bounds s (e+1) r.min_prefix_len.val hq (by omega)).2
  rcases ipnet.ipv4_broadcast_nat_spec net hpBound with ⟨br,hbr,hbrv⟩
  rcases RangeNext.ipv4_saturating_add_spec br 1#u32 with ⟨next,hnext,hnextv⟩
  rcases IPv4SubnetStep.ipv4_eq_value next br with ⟨same,hsame,hsamev⟩
  let b := IPv4SubnetMath.blockSize s (e+1) r.min_prefix_len.val hq (by omega)
  have hcanon := IPv4SubnetMath.block_canonical s (e+1) r.min_prefix_len.val hq (by omega)
  have hfit := IPv4SubnetMath.block_fits s (e+1) r.min_prefix_len.val hq (by omega)
  have hbPos := IPv4SubnetMath.blockSize_pos s (e+1) r.min_prefix_len.val hq (by omega)
  have hbrEq : CidrModel.ipv4Value br + 1 = s + b := by
    rw [hbrv, haddr, hprefix]
    exact hcanon.2
  have hnextEq : CidrModel.ipv4Value next =
      min (CidrModel.ipv4Value br + 1) (2^32-1) := by
    simpa using hnextv
  have hsameEq : same ↔ CidrModel.ipv4Value next = CidrModel.ipv4Value br := hsamev
  have hbrBound : CidrModel.ipv4Value br < 2^32 := CidrModel.ipv4Value_bound br
  have heLimit : e < RangeMath.limit := by simpa [RangeMath.limit] using heBound
  have hfit' : s + b ≤ e + 1 := by simpa [b] using hfit
  have hbPos' : 0 < b := by simpa [b] using hbPos
  have hnextMin : CidrModel.ipv4Value next =
      min (CidrModel.ipv4Value br + 1) RangeMath.maxAddress := by
    simpa [RangeMath.maxAddress, RangeMath.limit] using hnextEq
  have hresidual :
      IPv4SubnetStateMath.residualBlock s e b =
        IPv4SubnetMath.residual s (e+1) r.min_prefix_len.val hq (by omega) := by
    exact IPv4SubnetStateMath.residualBlock_eq_selected s e r.min_prefix_len.val b
      hq hse rfl
  by_cases hlt : s < e
  · have hc : compare s e = Ordering.lt := Nat.compare_eq_lt.mpr hlt
    have hc' : compare (CidrModel.ipv4Value r.start)
        (CidrModel.ipv4Value r.end) = Ordering.lt := hc
    by_cases hb : same
    · have hsat : CidrModel.ipv4Value next = CidrModel.ipv4Value br := hsameEq.mp hb
      have hstate := IPv4SubnetStateMath.saturated_residual_empty s e b
        (CidrModel.ipv4Value br) (CidrModel.ipv4Value next)
        hse heLimit hbPos' hfit' hbrEq hnextMin hsat
      refine ⟨net, { r with start := next, «end» := RangeNext.zeroAddr }, ?_, ?_,
        hprefix, ?_, rfl⟩
      · simp [ipnet.ipnet.Ipv4Subnets.Insts.CoreIterTraitsIteratorIteratorIpv4Net.next,
          Comparisons.ipv4_partial_cmp_spec, hc', hnet, hbr, hnext, hsame, hb,
          RangeNext.ipv4_replace_zero_spec]
      · simpa [s] using congrArg CidrModel.ipv4Value haddr
      · simp only [remaining, RangeNext.zeroAddr_value]
        rw [← hresidual, hstate.1]
        exact hstate.2
    · have hunsat : CidrModel.ipv4Value next ≠ CidrModel.ipv4Value br := by
        intro heq
        exact hb (hsameEq.mpr heq)
      have hstate := IPv4SubnetStateMath.unsaturated_residual s e b
        (CidrModel.ipv4Value br) (CidrModel.ipv4Value next)
        hse heLimit hbPos' hfit' hbrEq hnextMin hunsat
      refine ⟨net, { r with start := next }, ?_, ?_, hprefix, ?_, rfl⟩
      · simp [ipnet.ipnet.Ipv4Subnets.Insts.CoreIterTraitsIteratorIteratorIpv4Net.next,
          Comparisons.ipv4_partial_cmp_spec, hc', hnet, hbr, hnext, hsame, hb]
      · simpa [s] using congrArg CidrModel.ipv4Value haddr
      · simp only [remaining]
        rw [← hresidual]
        exact hstate
  · have heq : s = e := by omega
    have hc : compare s e = Ordering.eq := Nat.compare_eq_eq.mpr heq
    have hc' : compare (CidrModel.ipv4Value r.start)
        (CidrModel.ipv4Value r.end) = Ordering.eq := hc
    have hstate := IPv4SubnetStateMath.singleton_residual_empty s b
      (CidrModel.ipv4Value br) (CidrModel.ipv4Value next)
      (by omega : s < RangeMath.limit) hbPos'
      (by simpa [heq] using hfit') hbrEq hnextMin
    refine ⟨net, { r with start := next, «end» := RangeNext.zeroAddr }, ?_, ?_,
      hprefix, ?_, rfl⟩
    · simp [ipnet.ipnet.Ipv4Subnets.Insts.CoreIterTraitsIteratorIteratorIpv4Net.next,
        Comparisons.ipv4_partial_cmp_spec, hc', hnet, hbr, hnext,
        RangeNext.ipv4_replace_zero_spec]
    · simpa [s] using congrArg CidrModel.ipv4Value haddr
    · simp only [remaining, RangeNext.zeroAddr_value]
      rw [← hresidual, ← heq, hstate.1]
      exact hstate.2

end IPv4SubnetStep
