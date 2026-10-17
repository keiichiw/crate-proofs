module
public import Proofs.IPv4NetOps
public import Proofs.Core
public import Proofs.Comparisons
public import Proofs.RangeMath
public import Proofs.IPv4SubnetRangeBits

public section

open Aeneas Aeneas.Std Result

namespace IPv4SubnetStep

theorem u32_sub_ok (x y : U32) (h : y.val ≤ x.val) :
    ∃ z, x - y = Result.ok z ∧ z.val = x.val - y.val := by
  have hs : (x - y : Result U32) ⦃ z => z.val = x.val - y.val ⦄ := by
    apply WP.spec_mono (U32.sub_spec (x := x) (y := y) h)
    intro z hz
    exact hz.1
  cases hx : (x - y : Result U32) with
  | ret z =>
      refine ⟨z, rfl, ?_⟩
      simpa [hx] using hs
  | vis _ _ => simp [hx] at hs
  | div => simp [hx] at hs

theorem u32_add_ok (x y : U32) (h : x.val + y.val < 2^32) :
    ∃ z, x + y = Result.ok z ∧ z.val = x.val + y.val := by
  have hs : (x + y : Result U32) ⦃ z => z.val = x.val + y.val ⦄ := by
    apply U32.add_spec
    simp only [U32.max_eq]
    norm_num at h ⊢
    omega
  cases hx : (x + y : Result U32) with
  | ret z =>
      refine ⟨z, rfl, ?_⟩
      simpa [hx] using hs
  | vis _ _ => simp [hx] at hs
  | div => simp [hx] at hs

theorem u32_to_u8_value (x : U32) (h : x.val ≤ 32) :
    (UScalar.cast .U8 x).val = x.val := by
  rw [UScalar.cast_val_eq]
  have : x.val < 2^8 := by omega
  exact Nat.mod_eq_of_lt this

theorem u8_max_ok (x y : U8) :
    ∃ z, core.cmp.max core.cmp.OrdU8 x y = Result.ok z ∧
      z.val = max x.val y.val := by
  refine ⟨core.cmp.impls.OrdU8.max x y, ?_, ?_⟩
  · simp [core.cmp.max, liftFun2]
  · exact core.cmp.impls.OrdU8.max_val x y

/-- The reviewed fixed-width trailing-zero model returns the exact bit count
    encoded by reverse-and-leading-zero. -/
theorem trailing_zeros_spec (x : U32) :
    core.num.U32.trailing_zeros x =
      Result.ok ⟨BitVec.leadingZeros x.bv.reverse⟩ := by
  rfl

/-- The actual extracted Rust `trailing_ones` body complements its input and
    calls `trailing_zeros`. -/
theorem trailing_ones_spec (x : U32) :
    ipnet.core.num.U32.trailing_ones x =
      Result.ok ⟨BitVec.leadingZeros (~~~x).bv.reverse⟩ := by
  simp [ipnet.core.num.U32.trailing_ones, core.num.U32.trailing_zeros,
    lift, bind_ok]

/-- The two bit-count thresholds computed by the Rust helper select exactly
    the least eligible prefix in the independent dyadic model. -/
theorem best_prefix_from_counts (s e q : Nat) (hq : q ≤ 32) (hse : s ≤ e)
    (x range ones tz : U32)
    (hx : x.val = s) (hr : range.val = e - s)
    (hones : ipnet.core.num.U32.trailing_ones range = Result.ok ones)
    (htz : core.num.U32.trailing_zeros x = Result.ok tz) :
    IPv4SubnetMath.bestPrefix s (e+1) q hq (by omega) =
      max (max
        (if (core.num.U32.leading_zeros range).val + ones.val = 32
         then (core.num.U32.leading_zeros range).val
         else (core.num.U32.leading_zeros range).val + 1)
        (32 - tz.val)) q := by
  apply IPv4SubnetMath.best_eq_max_of_thresholds s (e+1) q
    (if (core.num.U32.leading_zeros range).val + ones.val = 32
     then (core.num.U32.leading_zeros range).val
     else (core.num.U32.leading_zeros range).val + 1)
    (32 - tz.val) hq (by omega)
  · intro p hp
    rcases IPv4SubnetRangeBits.range_prefix_all range with ⟨o, ho, _, hall⟩
    have he : o = ones := Result.ok_injective (ho.symm.trans hones)
    have hiff := hall p hp
    have hiff' :
        (if (core.num.U32.leading_zeros range).val + ones.val = 32
         then (core.num.U32.leading_zeros range).val
         else (core.num.U32.leading_zeros range).val + 1) ≤ p ↔
           2 ^ (32-p) ≤ e - s + 1 := by
      simpa only [he, hr] using hiff
    exact hiff'.trans (by omega :
      (2 ^ (32-p) ≤ e - s + 1) ↔ s + 2 ^ (32-p) ≤ e + 1)
  · intro p hp
    rcases IPv4SubnetBits.start_prefix_alignment x p hp with ⟨z,hz,hiff⟩
    have he : z = tz := Result.ok_injective (hz.symm.trans htz)
    simpa only [he, hx] using hiff

theorem range_prefix_computation (range : U32) :
    ∃ ones rp, ipnet.core.num.U32.trailing_ones range = Result.ok ones ∧
      (do
        let lz ← lift (core.num.U32.leading_zeros range)
        let ones ← ipnet.core.num.U32.trailing_ones range
        let sum ← lz + ones
        if sum = core.num.U32.BITS then Result.ok lz else lz + 1#u32) =
          Result.ok rp ∧
      rp.val =
        (let lz := (core.num.U32.leading_zeros range).val
         if lz + ones.val = 32 then lz else lz+1) ∧ rp.val ≤ 32 := by
  let lz := core.num.U32.leading_zeros range
  rcases IPv4SubnetRangeBits.range_prefix_all range with ⟨ones,hones,honesB,hall⟩
  have hlzB : lz.val ≤ 32 := by
    dsimp [lz]
    rw [IPv4SubnetRangeBits.leading_zeros_value]
    simpa [BitVec.le_def] using (BitVec.clz_le (x := range.bv))
  have hsumB : lz.val + ones.val < 2^32 := by omega
  rcases u32_add_ok lz ones hsumB with ⟨sum,hsum,hsumV⟩
  have heq : (sum = core.num.U32.BITS) ↔ lz.val + ones.val = 32 := by
    constructor
    · intro he
      have hv := congrArg UScalar.val he
      simpa [hsumV, core.num.U32.BITS] using hv
    · intro hv
      apply UScalar.val_eq_imp
      simpa [hsumV, core.num.U32.BITS] using hv
  have hrB : (if lz.val + ones.val = 32 then lz.val else lz.val+1) ≤ 32 := by
    have h := (hall 32 (by omega)).2
    have : 2 ^ (32-32) ≤ range.val + 1 := by simp
    exact h this
  by_cases hc : lz.val + ones.val = 32
  · refine ⟨ones, lz, hones, ?_, ?_, ?_⟩
    · simp [lz, hones, hsum, (heq.mpr hc), lift, bind_ok]
    · simp [lz, hc]
    · simpa [hc] using hrB
  · have hlz1 : lz.val + 1 < 2^32 := by omega
    rcases u32_add_ok lz 1#u32 hlz1 with ⟨rp,hrp,hrpV⟩
    refine ⟨ones, rp, hones, ?_, ?_, ?_⟩
    · simp [lz, hones, hsum, (heq.not.mpr hc), hrp, lift, bind_ok]
    · simp [lz, hrpV, hc]
    · simpa [hrpV, hc] using hrB

/-- The extracted helper normally returns the largest aligned CIDR block fitting
    the nonempty raw interval and minimum prefix. -/
theorem next_ipv4_subnet_live_spec
    (start stop : ipnet.core.net.ip_addr.Ipv4Addr) (q : U8)
    (hse : CidrModel.ipv4Value start ≤ CidrModel.ipv4Value stop)
    (hq : q.val ≤ 32) :
    ∃ net, ipnet.ipnet.next_ipv4_subnet start stop q = Result.ok net ∧
      net.addr = start ∧
      net.prefix_len.val =
        IPv4SubnetMath.bestPrefix (CidrModel.ipv4Value start)
          (CidrModel.ipv4Value stop + 1) q.val hq (by omega) := by
  rcases AddressConversions.ipv4_into_u32_spec stop with ⟨e,he,hev⟩
  rcases AddressConversions.ipv4_into_u32_spec start with ⟨s,hs,hsv⟩
  have hle : s.val ≤ e.val := by omega
  rcases u32_sub_ok e s hle with ⟨range,hrange,hrangev⟩
  rcases range_prefix_computation range with ⟨ones,rp,hones,hrp,hrpv,hrpb⟩
  rcases IPv4SubnetBits.trailing_zeros_le_width s with ⟨tz,htz,htzb⟩
  have h32 : (32#u32).val = 32 := by decide
  rcases u32_sub_ok 32#u32 tz (by simpa [h32] using htzb) with ⟨sp,hsp,hspv⟩
  have hspb : sp.val ≤ 32 := by omega
  let rp8 : U8 := UScalar.cast .U8 rp
  let sp8 : U8 := UScalar.cast .U8 sp
  have hrp8 : rp8.val = rp.val := u32_to_u8_value rp hrpb
  have hsp8 : sp8.val = sp.val := u32_to_u8_value sp hspb
  rcases u8_max_ok rp8 sp8 with ⟨m,hm,hmv⟩
  rcases u8_max_ok m q with ⟨p,hp,hpv⟩
  have hm' : core.cmp.impls.OrdU8.max rp8 sp8 = m := by
    simpa [core.cmp.max, liftFun2] using hm
  have hp' : core.cmp.impls.OrdU8.max m q = p := by
    simpa [core.cmp.max, liftFun2] using hp
  have hpBound : p.val ≤ 32 := by omega
  have hbest := best_prefix_from_counts s.val e.val q.val hq hle
    s range ones tz rfl hrangev hones htz
  have hpBest : p.val =
      IPv4SubnetMath.bestPrefix (CidrModel.ipv4Value start)
        (CidrModel.ipv4Value stop + 1) q.val hq (by omega) := by
    have hbest' :
        IPv4SubnetMath.bestPrefix (CidrModel.ipv4Value start)
          (CidrModel.ipv4Value stop + 1) q.val hq (by omega) =
        max (max
          (if (core.num.U32.leading_zeros range).val + ones.val = 32
           then (core.num.U32.leading_zeros range).val
           else (core.num.U32.leading_zeros range).val + 1)
          (32 - tz.val)) q.val := by
      simpa only [hsv, hev] using hbest
    rw [hbest']
    simp only [hpv, hmv, hrp8, hsp8, hrpv, hspv, h32]
  have hnew : ipnet.ipnet.Ipv4Net.new start p =
      Result.ok (.Ok { addr := start, prefix_len := p }) := by
    rcases ipnet.ipnet.ipv4_new_spec start p with ⟨out,hout,houtv⟩
    simpa [hpBound] using hout.trans (congrArg Result.ok houtv)
  refine ⟨{ addr := start, prefix_len := p }, ?_, rfl, hpBest⟩
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
  rcases u32_add_ok (core.num.U32.leading_zeros range) ones
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


/-- Independent meaning of a raw subnet iterator's remaining addresses. -/
@[expose] def remaining (r : ipnet.ipnet.Ipv4Subnets) : RangeMath.HalfOpen :=
  RangeMath.ofInclusive (CidrModel.ipv4Value r.start) (CidrModel.ipv4Value r.end)

theorem constructor_remaining (start stop : ipnet.core.net.ip_addr.Ipv4Addr)
    (q : U8) :
    ipnet.ipnet.Ipv4Subnets.new start stop q =
      Result.ok { start := start, «end» := stop, min_prefix_len := q } := by
  rfl

/-- Reversed raw endpoints are exhausted for every stored prefix, including
    an otherwise invalid one. The actual iterator body leaves the state alone. -/
theorem next_empty_spec (r : ipnet.ipnet.Ipv4Subnets)
    (h : CidrModel.ipv4Value r.end < CidrModel.ipv4Value r.start) :
    ipnet.ipnet.Ipv4Subnets.Insts.CoreIterTraitsIteratorIteratorIpv4Net.next r =
      Result.ok (none, r) ∧ remaining r = .empty := by
  have hc : compare (CidrModel.ipv4Value r.start)
      (CidrModel.ipv4Value r.end) = Ordering.gt := Nat.compare_eq_gt.mpr h
  constructor
  · simp [ipnet.ipnet.Ipv4Subnets.Insts.CoreIterTraitsIteratorIteratorIpv4Net.next,
      Comparisons.ipv4_partial_cmp_spec, hc]
  · simp [remaining, RangeMath.ofInclusive, Nat.not_le.mpr h]

end IPv4SubnetStep
