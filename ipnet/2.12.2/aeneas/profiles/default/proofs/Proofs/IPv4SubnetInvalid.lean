module
public import Proofs.IPv4SubnetStep

public section

open Aeneas Aeneas.Std Result

namespace IPv4SubnetInvalid

theorem ipv4_new_invalid (ip : ipnet.core.net.ip_addr.Ipv4Addr)
    (q : U8) (hq : 32 < q.val) :
    ipnet.ipnet.Ipv4Net.new ip q = Result.ok (.Err ()) := by
  simp [ipnet.ipnet.Ipv4Net.new, hq]

theorem ipv4_unwrap_invalid (ip : ipnet.core.net.ip_addr.Ipv4Addr)
    (q : U8) (hq : 32 < q.val) :
    (do
      let r ← ipnet.ipnet.Ipv4Net.new ip q
      core.result.Result.unwrap_without_debug r) =
      (Result.fail .panic : Result ipnet.ipnet.Ipv4Net) := by
  simp [ipv4_new_invalid ip q hq, core.result.Result.unwrap_without_debug]

theorem helper_invalid_live
    (start stop : ipnet.core.net.ip_addr.Ipv4Addr) (q : U8)
    (hse : CidrModel.ipv4Value start ≤ CidrModel.ipv4Value stop)
    (hq : 32 < q.val) :
    ipnet.ipnet.next_ipv4_subnet start stop q = Result.fail .panic := by
  rcases AddressConversions.ipv4_into_u32_spec stop with ⟨e,he,hev⟩
  rcases AddressConversions.ipv4_into_u32_spec start with ⟨s,hs,hsv⟩
  have hle : s.val ≤ e.val := by omega
  rcases IPv4SubnetStep.u32_sub_ok e s hle with ⟨range,hrange,hrangev⟩
  rcases IPv4SubnetStep.range_prefix_computation range with
    ⟨ones,rp,hones,hrp,hrpv,hrpb⟩
  rcases IPv4SubnetBits.trailing_zeros_le_width s with ⟨tz,htz,htzb⟩
  have h32 : (32#u32).val = 32 := by decide
  rcases IPv4SubnetStep.u32_sub_ok 32#u32 tz
      (by simpa [h32] using htzb) with ⟨sp,hsp,hspv⟩
  have hspb : sp.val ≤ 32 := by omega
  let rp8 : U8 := UScalar.cast .U8 rp
  let sp8 : U8 := UScalar.cast .U8 sp
  have hrp8 : rp8.val = rp.val := IPv4SubnetStep.u32_to_u8_value rp hrpb
  have hsp8 : sp8.val = sp.val := IPv4SubnetStep.u32_to_u8_value sp hspb
  rcases IPv4SubnetStep.u8_max_ok rp8 sp8 with ⟨m,hm,hmv⟩
  rcases IPv4SubnetStep.u8_max_ok m q with ⟨p,hp,hpv⟩
  have hm' : core.cmp.impls.OrdU8.max rp8 sp8 = m := by
    simpa [core.cmp.max, liftFun2] using hm
  have hp' : core.cmp.impls.OrdU8.max m q = p := by
    simpa [core.cmp.max, liftFun2] using hp
  have hpqv : p.val = q.val := by omega
  have hpq : p = q := UScalar.eq_of_val_eq hpqv
  have hnew : ipnet.ipnet.Ipv4Net.new start p = Result.ok (.Err ()) := by
    rw [hpq]
    exact ipv4_new_invalid start q hq
  have hrp' :
      (do
        let sum ← core.num.U32.leading_zeros range + ones
        if sum = core.num.U32.BITS then Result.ok (core.num.U32.leading_zeros range)
        else core.num.U32.leading_zeros range + 1#u32) = Result.ok rp := by
    simpa [hones, lift, bind_ok] using hrp
  have honesBound : ones.val ≤ 32 := by
    rcases IPv4SubnetRangeBits.range_prefix_all range with ⟨o,ho,hob,_⟩
    have heq : o = ones := Result.ok_injective (ho.symm.trans hones)
    simpa [heq] using hob
  have hlzBound : (core.num.U32.leading_zeros range).val ≤ 32 := by
    rw [IPv4SubnetRangeBits.leading_zeros_value]
    simpa [BitVec.le_def] using (BitVec.clz_le (x := range.bv))
  rcases IPv4SubnetStep.u32_add_ok (core.num.U32.leading_zeros range) ones
      (by omega) with ⟨sum,hsum,hsumv⟩
  by_cases hc : sum = core.num.U32.BITS
  · have hrpeq : rp = core.num.U32.leading_zeros range := by
      simpa [hsum, hc] using hrp'.symm
    subst rp
    simp [ipnet.ipnet.next_ipv4_subnet, he, hs, hrange, hones, htz,
      hsp, hsum, hc, lift, bind_ok]
    dsimp [rp8, sp8] at hm'
    simp [hm', hp', hnew, core.result.Result.unwrap_without_debug]
  · have hadd : core.num.U32.leading_zeros range + 1#u32 = Result.ok rp := by
      simpa [hsum, hc] using hrp'
    simp [ipnet.ipnet.next_ipv4_subnet, he, hs, hrange, hones, htz,
      hsp, hsum, hc, hadd, lift, bind_ok]
    dsimp [rp8, sp8] at hm'
    simp [hm', hp', hnew, core.result.Result.unwrap_without_debug]

theorem next_invalid_live (r : ipnet.ipnet.Ipv4Subnets)
    (hse : CidrModel.ipv4Value r.start ≤ CidrModel.ipv4Value r.end)
    (hq : 32 < r.min_prefix_len.val) :
    ipnet.ipnet.Ipv4Subnets.Insts.CoreIterTraitsIteratorIteratorIpv4Net.next r =
      Result.fail .panic := by
  rcases Nat.lt_or_eq_of_le hse with hlt | heq
  · have hc : compare (CidrModel.ipv4Value r.start)
        (CidrModel.ipv4Value r.end) = Ordering.lt := Nat.compare_eq_lt.mpr hlt
    simp [ipnet.ipnet.Ipv4Subnets.Insts.CoreIterTraitsIteratorIteratorIpv4Net.next,
      Comparisons.ipv4_partial_cmp_spec, hc,
      helper_invalid_live r.start r.end r.min_prefix_len hse hq]
  · have hc : compare (CidrModel.ipv4Value r.start)
        (CidrModel.ipv4Value r.end) = Ordering.eq := Nat.compare_eq_eq.mpr heq
    simp [ipnet.ipnet.Ipv4Subnets.Insts.CoreIterTraitsIteratorIteratorIpv4Net.next,
      Comparisons.ipv4_partial_cmp_spec, hc,
      helper_invalid_live r.start r.end r.min_prefix_len hse hq]

end IPv4SubnetInvalid
