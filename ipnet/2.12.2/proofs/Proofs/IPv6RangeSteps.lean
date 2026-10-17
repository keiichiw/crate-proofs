module
public import Proofs.IPv6RangeBasic
public import Proofs.IPv6ConstructorMath
public import Proofs.RangeMore
public section

open Aeneas Aeneas.Std Result

namespace IPv6RangeSteps

/-- Numeric meaning of the actual public saturating IPv6 address addition. -/
theorem ipv6_saturating_add_spec
    (a : ipnet.core.net.ip_addr.Ipv6Addr) (rhs : U128) :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpAddU128Ipv6Addr.saturating_add a rhs =
        Result.ok out ∧
      CidrModel.ipv6Value out = min (CidrModel.ipv6Value a + rhs.val) (2^128 - 1) := by
  rcases AddressConversions.ipv6_into_u128_spec a with ⟨x, hx, hxv⟩
  rcases AddressConversions.ipv6_from_u128_spec (core.num.U128.saturating_add x rhs) with
    ⟨out, hout, houtv⟩
  refine ⟨out, ?_, ?_⟩
  · simp [ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpAddU128Ipv6Addr.saturating_add,
      core.convert.IntoFrom.into, hx, hout, lift, bind_ok]
  · rw [houtv, core.num.U128.saturating_add_val, hxv]

theorem ipv6_add_one_spec (a : ipnet.core.net.ip_addr.Ipv6Addr) :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpStep.add_one a = Result.ok out ∧
      CidrModel.ipv6Value out = min (CidrModel.ipv6Value a + 1) (2^128 - 1) := by
  simpa [ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpStep.add_one] using
    ipv6_saturating_add_spec a 1#u128

/-- Numeric meaning of the actual public saturating IPv6 address subtraction. -/
theorem ipv6_saturating_sub_spec
    (a : ipnet.core.net.ip_addr.Ipv6Addr) (rhs : U128) :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpSubU128Ipv6Addr.saturating_sub a rhs =
        Result.ok out ∧
      CidrModel.ipv6Value out = CidrModel.ipv6Value a - rhs.val := by
  rcases AddressConversions.ipv6_into_u128_spec a with ⟨x, hx, hxv⟩
  rcases AddressConversions.ipv6_from_u128_spec (core.num.U128.saturating_sub x rhs) with
    ⟨out, hout, houtv⟩
  refine ⟨out, ?_, ?_⟩
  · simp [ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpSubU128Ipv6Addr.saturating_sub,
      core.convert.IntoFrom.into, hx, hout, lift, bind_ok]
  · rw [houtv, core.num.U128.saturating_sub_val, hxv]

theorem ipv6_sub_one_spec (a : ipnet.core.net.ip_addr.Ipv6Addr) :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpStep.sub_one a = Result.ok out ∧
      CidrModel.ipv6Value out = CidrModel.ipv6Value a - 1 := by
  simpa [ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpStep.sub_one] using
    ipv6_saturating_sub_spec a 1#u128

@[expose] def remaining (r : ipnet.ipext.Ipv6AddrRange) : RangeMath.HalfOpen :=
  IPv6RangeMath.remaining (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end)

theorem constructor_remaining
    (start stop : ipnet.core.net.ip_addr.Ipv6Addr) :
    ∃ r, ipnet.ipext.Ipv6AddrRange.new start stop = Result.ok r ∧
      remaining r = IPv6RangeMath.remaining
        (CidrModel.ipv6Value start) (CidrModel.ipv6Value stop) := by
  exact ⟨{ start := start, «end» := stop }, rfl, rfl⟩

theorem ipv6_replace_zero_spec (a : ipnet.core.net.ip_addr.Ipv6Addr) :
    ∃ zero,
      ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpStep.replace_zero a =
        Result.ok (a, zero) ∧ CidrModel.ipv6Value zero = 0 := by
  rcases IPv6ConstructorMath.ipv6_new_zero_spec with ⟨zero, hzero, hvalue⟩
  refine ⟨zero, ?_, hvalue⟩
  simp [ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpStep.replace_zero,
    hzero, core.mem.replace]

theorem ipv6_replace_one_spec (a : ipnet.core.net.ip_addr.Ipv6Addr) :
    ∃ one,
      ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpStep.replace_one a =
        Result.ok (a, one) ∧ CidrModel.ipv6Value one = 1 := by
  rcases IPv6ConstructorMath.ipv6_new_one_spec with ⟨one, hone, hvalue⟩
  refine ⟨one, ?_, hvalue⟩
  simp [ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpStep.replace_one,
    hone, core.mem.replace]

/-- The actual IPv6 iterator step returns the first address and updates the
    independent half-open remaining interval, for every raw pair of endpoints. -/
theorem range_next_spec (r : ipnet.ipext.Ipv6AddrRange) :
    ∃ out r',
      ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.next r =
        Result.ok (out, r') ∧
      (out.map CidrModel.ipv6Value, remaining r') =
        RangeMath.next (remaining r) := by
  let s := CidrModel.ipv6Value r.start
  let e := CidrModel.ipv6Value r.end
  by_cases hlt : s < e
  · have hc : compare (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end) =
        Ordering.lt := Nat.compare_eq_lt.mpr hlt
    rcases ipv6_add_one_spec r.start with ⟨next, hnext, hnextv⟩
    have he : e < IPv6RangeMath.limit := by
      simpa [IPv6RangeMath.limit] using CidrModel.ipv6Value_bound r.end
    have hsuc : min (s + 1) (2^128 - 1) = s + 1 := by
      apply Nat.min_eq_left
      dsimp [IPv6RangeMath.limit] at he
      omega
    refine ⟨some r.start, { r with start := next }, ?_, ?_⟩
    · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.next,
        Comparisons.ipv6_partial_cmp_spec, hc, hnext, core.mem.replace]
    · change (some s, RangeMath.ofInclusive (CidrModel.ipv6Value next) e) =
        RangeMath.next (RangeMath.ofInclusive s e)
      rw [hnextv, hsuc, RangeMath.next_lt s e hlt]
  · by_cases heq : s = e
    · have hc : compare (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end) =
          Ordering.eq := Nat.compare_eq_eq.mpr heq
      rcases ipv6_replace_zero_spec r.end with ⟨zero, hzero, hzerov⟩
      rcases ipv6_replace_one_spec r.start with ⟨one, hone, honev⟩
      refine ⟨some r.start, { start := one, «end» := zero }, ?_, ?_⟩
      · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.next,
          Comparisons.ipv6_partial_cmp_spec, hc, hzero, hone]
      · change (some s, RangeMath.ofInclusive (CidrModel.ipv6Value one)
          (CidrModel.ipv6Value zero)) = RangeMath.next (RangeMath.ofInclusive s e)
        rw [honev, hzerov, RangeMath.sentinel_empty, ← heq, RangeMath.next_eq]
    · have hgt : e < s := by omega
      have hc : compare (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end) =
          Ordering.gt := Nat.compare_eq_gt.mpr hgt
      refine ⟨none, r, ?_, ?_⟩
      · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.next,
          Comparisons.ipv6_partial_cmp_spec, hc]
      · change (none, RangeMath.ofInclusive s e) = RangeMath.next (RangeMath.ofInclusive s e)
        rw [RangeMath.next_gt s e hgt]
        simp [RangeMath.ofInclusive, Nat.not_le.mpr hgt]

/-- The extracted double-ended step returns the last remaining IPv6 address
    and updates the independent interval, including the singleton sentinel. -/
theorem range_next_back_spec (r : ipnet.ipext.Ipv6AddrRange) :
    ∃ out r',
      ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv6Addr.next_back r =
        Result.ok (out, r') ∧
      (out.map CidrModel.ipv6Value, remaining r') =
        RangeMore.backStep (remaining r) := by
  let s := CidrModel.ipv6Value r.start
  let e := CidrModel.ipv6Value r.end
  by_cases hlt : s < e
  · have hc : compare (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end) =
        Ordering.lt := Nat.compare_eq_lt.mpr hlt
    rcases ipv6_sub_one_spec r.end with ⟨prev, hprev, hprevv⟩
    refine ⟨some r.end, { r with «end» := prev }, ?_, ?_⟩
    · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv6Addr.next_back,
        Comparisons.ipv6_partial_cmp_spec, hc, hprev, core.mem.replace]
    · change (some e, RangeMath.ofInclusive s (CidrModel.ipv6Value prev)) =
        RangeMore.backStep (RangeMath.ofInclusive s e)
      rw [hprevv, RangeMore.backStep_lt s e hlt]
  · by_cases heq : s = e
    · have hc : compare (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end) =
          Ordering.eq := Nat.compare_eq_eq.mpr heq
      rcases ipv6_replace_zero_spec r.end with ⟨zero, hzero, hzerov⟩
      rcases ipv6_replace_one_spec r.start with ⟨one, hone, honev⟩
      refine ⟨some r.start, { start := one, «end» := zero }, ?_, ?_⟩
      · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv6Addr.next_back,
          Comparisons.ipv6_partial_cmp_spec, hc, hzero, hone]
      · change (some s, RangeMath.ofInclusive (CidrModel.ipv6Value one)
          (CidrModel.ipv6Value zero)) = RangeMore.backStep (RangeMath.ofInclusive s e)
        rw [honev, hzerov, RangeMath.sentinel_empty, ← heq, RangeMore.backStep_eq]
    · have hgt : e < s := by omega
      have hc : compare (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end) =
          Ordering.gt := Nat.compare_eq_gt.mpr hgt
      refine ⟨none, r, ?_, ?_⟩
      · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv6Addr.next_back,
          Comparisons.ipv6_partial_cmp_spec, hc]
      · change (none, RangeMath.ofInclusive s e) = RangeMore.backStep (RangeMath.ofInclusive s e)
        rw [RangeMore.backStep_gt s e hgt]
        simp [RangeMath.ofInclusive, Nat.not_le.mpr hgt]

/-- Exhaustion is preserved by either actual front or back step. -/
theorem range_empty_no_revival (r : ipnet.ipext.Ipv6AddrRange)
    (hempty : remaining r = .empty) :
    (∃ r',
      ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.next r =
        Result.ok (none, r') ∧ remaining r' = .empty) ∧
    (∃ r',
      ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv6Addr.next_back r =
        Result.ok (none, r') ∧ remaining r' = .empty) := by
  rcases range_next_spec r with ⟨outF, rF, hF, hvF⟩
  rcases range_next_back_spec r with ⟨outB, rB, hB, hvB⟩
  rw [hempty] at hvF hvB
  simp [RangeMath.next, RangeMore.backStep] at hvF hvB
  cases outF <;> cases outB <;> simp_all

end IPv6RangeSteps
