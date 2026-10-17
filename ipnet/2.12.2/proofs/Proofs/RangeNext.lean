module
public import Proofs.Contains
public import Proofs.Collections
public import Proofs.RangeMath
public section

open Aeneas Aeneas.Std Result

namespace RangeNext

theorem u32_saturating_add_value (x y : U32) :
    (core.num.U32.saturating_add x y).val =
      min (x.val + y.val) (2^32 - 1) :=
  core.num.U32.saturating_add_val x y

theorem ipv4_saturating_add_spec (a : ipnet.core.net.ip_addr.Ipv4Addr) (rhs : U32) :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpAddU32Ipv4Addr.saturating_add a rhs =
        Result.ok out ∧
      CidrModel.ipv4Value out = min (CidrModel.ipv4Value a + rhs.val) (2^32 - 1) := by
  rcases AddressConversions.ipv4_into_u32_spec a with ⟨x, hx, hxv⟩
  rcases AddressConversions.ipv4_from_u32_spec (core.num.U32.saturating_add x rhs) with
    ⟨out, hout, houtv⟩
  refine ⟨out, ?_, ?_⟩
  · simp [ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpAddU32Ipv4Addr.saturating_add,
      core.convert.IntoFrom.into, hx, hout,
      lift, bind_ok]
  · rw [houtv, u32_saturating_add_value, hxv]

theorem ipv4_add_one_spec (a : ipnet.core.net.ip_addr.Ipv4Addr) :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpStep.add_one a = Result.ok out ∧
      CidrModel.ipv4Value out = min (CidrModel.ipv4Value a + 1) (2^32 - 1) := by
  simpa [ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpStep.add_one] using
    ipv4_saturating_add_spec a 1#u32

def zeroAddr : ipnet.core.net.ip_addr.Ipv4Addr :=
  { octets := Array.make 4#usize [0#u8, 0#u8, 0#u8, 0#u8] }

def oneAddr : ipnet.core.net.ip_addr.Ipv4Addr :=
  { octets := Array.make 4#usize [0#u8, 0#u8, 0#u8, 1#u8] }

theorem zeroAddr_value : CidrModel.ipv4Value zeroAddr = 0 := by decide
theorem oneAddr_value : CidrModel.ipv4Value oneAddr = 1 := by decide

theorem ipv4_replace_zero_spec (a : ipnet.core.net.ip_addr.Ipv4Addr) :
    ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpStep.replace_zero a =
      Result.ok (a, zeroAddr) := by
  simp [ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpStep.replace_zero,
    ipnet.core.net.ip_addr.Ipv4Addr.new, core.mem.replace, zeroAddr]

theorem ipv4_replace_one_spec (a : ipnet.core.net.ip_addr.Ipv4Addr) :
    ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpStep.replace_one a =
      Result.ok (a, oneAddr) := by
  simp [ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpStep.replace_one,
    ipnet.core.net.ip_addr.Ipv4Addr.new, core.mem.replace, oneAddr]

/-- Independent meaning of every raw inclusive IPv4 range state. -/
@[expose] def remaining (r : ipnet.ipext.Ipv4AddrRange) : RangeMath.HalfOpen :=
  RangeMath.ofInclusive (CidrModel.ipv4Value r.start) (CidrModel.ipv4Value r.end)

theorem constructor_remaining (start stop : ipnet.core.net.ip_addr.Ipv4Addr) :
    ∃ r, ipnet.ipext.Ipv4AddrRange.new start stop = Result.ok r ∧
      remaining r = RangeMath.ofInclusive
        (CidrModel.ipv4Value start) (CidrModel.ipv4Value stop) := by
  exact ⟨{ start := start, «end» := stop }, rfl, rfl⟩

/-- The actual extracted Iterator body returns the first remaining address and
    updates the remaining half-open interval by exactly one step. -/
theorem range_next_spec (r : ipnet.ipext.Ipv4AddrRange) :
    ∃ out r',
      ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.next r =
        Result.ok (out, r') ∧
      (out.map CidrModel.ipv4Value, remaining r') =
        RangeMath.next (remaining r) := by
  let s := CidrModel.ipv4Value r.start
  let e := CidrModel.ipv4Value r.end
  by_cases hlt : s < e
  · have hc : compare s e = Ordering.lt := Nat.compare_eq_lt.mpr hlt
    have hc' : compare (CidrModel.ipv4Value r.start) (CidrModel.ipv4Value r.end) = Ordering.lt := hc
    rcases ipv4_add_one_spec r.start with ⟨next, hnext, hnextv⟩
    have he : e < RangeMath.limit := by
      simpa [RangeMath.limit] using CidrModel.ipv4Value_bound r.end
    have hsucc : min (s + 1) (2^32 - 1) = s + 1 := by
      simpa [RangeMath.saturatingSucc, RangeMath.maxAddress, RangeMath.limit] using
        RangeMath.saturatingSucc_lt s e hlt he
    refine ⟨some r.start, { r with start := next }, ?_, ?_⟩
    · simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.next,
        Comparisons.ipv4_partial_cmp_spec, hc', hnext, core.mem.replace]
    · change (some s, RangeMath.ofInclusive (CidrModel.ipv4Value next) e) =
        RangeMath.next (RangeMath.ofInclusive s e)
      rw [hnextv, hsucc, RangeMath.next_lt s e hlt]
  · by_cases heq : s = e
    · have hc : compare s e = Ordering.eq := Nat.compare_eq_eq.mpr heq
      have hc' : compare (CidrModel.ipv4Value r.start) (CidrModel.ipv4Value r.end) = Ordering.eq := hc
      refine ⟨some r.start, { start := oneAddr, «end» := zeroAddr }, ?_, ?_⟩
      · simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.next,
          Comparisons.ipv4_partial_cmp_spec, hc',
          ipv4_replace_zero_spec, ipv4_replace_one_spec]
      · change (some s, RangeMath.ofInclusive (CidrModel.ipv4Value oneAddr)
          (CidrModel.ipv4Value zeroAddr)) = RangeMath.next (RangeMath.ofInclusive s e)
        rw [oneAddr_value, zeroAddr_value, RangeMath.sentinel_empty, ← heq,
          RangeMath.next_eq]
    · have hgt : e < s := by omega
      have hc : compare s e = Ordering.gt := Nat.compare_eq_gt.mpr hgt
      have hc' : compare (CidrModel.ipv4Value r.start) (CidrModel.ipv4Value r.end) = Ordering.gt := hc
      refine ⟨none, r, ?_, ?_⟩
      · simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.next,
          Comparisons.ipv4_partial_cmp_spec, hc']
      · change (none, RangeMath.ofInclusive s e) = RangeMath.next (RangeMath.ofInclusive s e)
        rw [RangeMath.next_gt s e hgt]
        simp [RangeMath.ofInclusive, Nat.not_le.mpr hgt]

end RangeNext
