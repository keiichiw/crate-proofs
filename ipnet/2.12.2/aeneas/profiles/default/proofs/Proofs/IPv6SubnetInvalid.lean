module
public import Proofs.IPv6SubnetStep

public section

open Aeneas Aeneas.Std Result

namespace IPv6SubnetInvalid

theorem ipv6_new_invalid (ip : ipnet.core.net.ip_addr.Ipv6Addr)
    (q : U8) (hq : 128 < q.val) :
    ipnet.ipnet.Ipv6Net.new ip q = Result.ok (.Err ()) := by
  simp [ipnet.ipnet.Ipv6Net.new, hq]

theorem ipv6_unwrap_invalid (ip : ipnet.core.net.ip_addr.Ipv6Addr)
    (q : U8) (hq : 128 < q.val) :
    (do
      let r ← ipnet.ipnet.Ipv6Net.new ip q
      core.result.Result.unwrap_without_debug r) =
      (Result.fail .panic : Result ipnet.ipnet.Ipv6Net) := by
  simp [ipv6_new_invalid ip q hq, core.result.Result.unwrap_without_debug]

theorem helper_invalid_live
    (start stop : ipnet.core.net.ip_addr.Ipv6Addr) (q : U8)
    (hse : CidrModel.ipv6Value start ≤ CidrModel.ipv6Value stop)
    (hq : 128 < q.val) :
    ipnet.ipnet.next_ipv6_subnet start stop q = Result.fail .panic := by
  rcases AddressConversions.ipv6_into_u128_spec stop with ⟨e,he,hev⟩
  rcases AddressConversions.ipv6_into_u128_spec start with ⟨s,hs,hsv⟩
  have hle : s.val ≤ e.val := by omega
  rcases IPv6SubnetStep.u128_sub_ok e s hle with ⟨range,hrange,hrangev⟩
  rcases IPv6SubnetStep.range_prefix_computation range with
    ⟨ones,rp,hones,hrp,hrpv,hrpb⟩
  rcases IPv6SubnetBits.trailing_zeros_le_width s with ⟨tz,htz,htzb⟩
  have h128 : (128#u32).val = 128 := by decide
  rcases IPv4SubnetStep.u32_sub_ok 128#u32 tz
      (by simpa [h128] using htzb) with ⟨sp,hsp,hspv⟩
  have hspb : sp.val ≤ 128 := by omega
  let rp8 : U8 := UScalar.cast .U8 rp
  let sp8 : U8 := UScalar.cast .U8 sp
  have hrp8 : rp8.val = rp.val := IPv6SubnetStep.u32_to_u8_value rp hrpb
  have hsp8 : sp8.val = sp.val := IPv6SubnetStep.u32_to_u8_value sp hspb
  rcases IPv4SubnetStep.u8_max_ok rp8 sp8 with ⟨m,hm,hmv⟩
  rcases IPv4SubnetStep.u8_max_ok m q with ⟨p,hp,hpv⟩
  have hm' : core.cmp.impls.OrdU8.max rp8 sp8 = m := by
    simpa [core.cmp.max, liftFun2] using hm
  have hp' : core.cmp.impls.OrdU8.max m q = p := by
    simpa [core.cmp.max, liftFun2] using hp
  have hpqv : p.val = q.val := by omega
  have hpq : p = q := UScalar.eq_of_val_eq hpqv
  have hnew : ipnet.ipnet.Ipv6Net.new start p = Result.ok (.Err ()) := by
    rw [hpq]
    exact ipv6_new_invalid start q hq
  have hrp' :
      (do
        let sum ← core.num.U128.leading_zeros range + ones
        if sum = core.num.U128.BITS then Result.ok (core.num.U128.leading_zeros range)
        else core.num.U128.leading_zeros range + 1#u32) = Result.ok rp := by
    simpa [hones, lift, bind_ok] using hrp
  have honesBound : ones.val ≤ 128 := by
    rcases IPv6SubnetRangeBits.range_prefix_all range with ⟨o,ho,hob,_⟩
    have heq : o = ones := Result.ok_injective (ho.symm.trans hones)
    simpa [heq] using hob
  have hlzBound : (core.num.U128.leading_zeros range).val ≤ 128 := by
    rw [IPv6SubnetRangeBits.leading_zeros_value]
    simpa [BitVec.le_def] using (BitVec.clz_le (x := range.bv))
  rcases IPv4SubnetStep.u32_add_ok (core.num.U128.leading_zeros range) ones
      (by omega) with ⟨sum,hsum,hsumv⟩
  by_cases hc : sum = core.num.U128.BITS
  · have hrpeq : rp = core.num.U128.leading_zeros range := by
      simpa [hsum, hc] using hrp'.symm
    subst rp
    simp [ipnet.ipnet.next_ipv6_subnet, he, hs, hrange, hones, htz,
      hsp, hsum, hc, lift, bind_ok]
    dsimp [rp8, sp8] at hm'
    simp [hm', hp', hnew, core.result.Result.unwrap_without_debug]
  · have hadd : core.num.U128.leading_zeros range + 1#u32 = Result.ok rp := by
      simpa [hsum, hc] using hrp'
    simp [ipnet.ipnet.next_ipv6_subnet, he, hs, hrange, hones, htz,
      hsp, hsum, hc, hadd, lift, bind_ok]
    dsimp [rp8, sp8] at hm'
    simp [hm', hp', hnew, core.result.Result.unwrap_without_debug]

theorem next_invalid_live (r : ipnet.ipnet.Ipv6Subnets)
    (hse : CidrModel.ipv6Value r.start ≤ CidrModel.ipv6Value r.end)
    (hq : 128 < r.min_prefix_len.val) :
    ipnet.ipnet.Ipv6Subnets.Insts.CoreIterTraitsIteratorIteratorIpv6Net.next r =
      Result.fail .panic := by
  rcases Nat.lt_or_eq_of_le hse with hlt | heq
  · have hc : compare (CidrModel.ipv6Value r.start)
        (CidrModel.ipv6Value r.end) = Ordering.lt := Nat.compare_eq_lt.mpr hlt
    simp [ipnet.ipnet.Ipv6Subnets.Insts.CoreIterTraitsIteratorIteratorIpv6Net.next,
      Comparisons.ipv6_partial_cmp_spec, hc,
      helper_invalid_live r.start r.end r.min_prefix_len hse hq]
  · have hc : compare (CidrModel.ipv6Value r.start)
        (CidrModel.ipv6Value r.end) = Ordering.eq := Nat.compare_eq_eq.mpr heq
    simp [ipnet.ipnet.Ipv6Subnets.Insts.CoreIterTraitsIteratorIteratorIpv6Net.next,
      Comparisons.ipv6_partial_cmp_spec, hc,
      helper_invalid_live r.start r.end r.min_prefix_len hse hq]

end IPv6SubnetInvalid
