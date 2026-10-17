module
public import Proofs.RangeNext
public section

open Aeneas Aeneas.Std Result

namespace RangeMore

theorem ipv4_saturating_sub_spec (a : ipnet.core.net.ip_addr.Ipv4Addr) (rhs : U32) :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpSubU32Ipv4Addr.saturating_sub a rhs =
        Result.ok out ∧
      CidrModel.ipv4Value out = CidrModel.ipv4Value a - rhs.val := by
  rcases AddressConversions.ipv4_into_u32_spec a with ⟨x, hx, hxv⟩
  rcases AddressConversions.ipv4_from_u32_spec (core.num.U32.saturating_sub x rhs) with
    ⟨out, hout, houtv⟩
  refine ⟨out, ?_, ?_⟩
  · simp [ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpSubU32Ipv4Addr.saturating_sub,
      core.convert.IntoFrom.into, hx, hout, lift, bind_ok]
  · rw [houtv, core.num.U32.saturating_sub_val, hxv]

theorem ipv4_saturating_sub_addr_spec
    (a b : ipnet.core.net.ip_addr.Ipv4Addr) :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpSubIpv4AddrU32.saturating_sub a b =
        Result.ok out ∧
      out.val = CidrModel.ipv4Value a - CidrModel.ipv4Value b := by
  rcases AddressConversions.ipv4_into_u32_spec a with ⟨x, hx, hxv⟩
  rcases AddressConversions.ipv4_into_u32_spec b with ⟨y, hy, hyv⟩
  refine ⟨core.num.U32.saturating_sub x y, ?_, ?_⟩
  · simp [ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpSubIpv4AddrU32.saturating_sub,
      core.convert.IntoFrom.into, hx, hy, lift, bind_ok]
  · rw [core.num.U32.saturating_sub_val, hxv, hyv]

theorem ipv4_sub_one_spec (a : ipnet.core.net.ip_addr.Ipv4Addr) :
    ∃ out, ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpStep.sub_one a = Result.ok out ∧
      CidrModel.ipv4Value out = CidrModel.ipv4Value a - 1 := by
  simpa [ipnet.core.net.ip_addr.Ipv4Addr.Insts.IpnetIpextIpStep.sub_one] using
    ipv4_saturating_sub_spec a 1#u32

@[expose] def backStep : RangeMath.HalfOpen → Option Nat × RangeMath.HalfOpen
  | .empty => (none, .empty)
  | .live lo hi =>
      if lo < hi then
        (some (hi - 1), if lo < hi - 1 then .live lo (hi - 1) else .empty)
      else (none, .empty)

theorem backStep_lt (s e : Nat) (h : s < e) :
    backStep (RangeMath.ofInclusive s e) =
      (some e, RangeMath.ofInclusive s (e - 1)) := by
  have hle : s ≤ e := Nat.le_of_lt h
  have hle' : s ≤ e - 1 := by omega
  simp [backStep, RangeMath.ofInclusive, hle, h, hle']
  omega

theorem backStep_eq (s : Nat) :
    backStep (RangeMath.ofInclusive s s) = (some s, .empty) := by
  simp [backStep, RangeMath.ofInclusive]

theorem backStep_gt (s e : Nat) (h : e < s) :
    backStep (RangeMath.ofInclusive s e) = (none, .empty) := by
  simp [backStep, RangeMath.ofInclusive, Nat.not_le.mpr h]

theorem range_next_back_spec (r : ipnet.ipext.Ipv4AddrRange) :
    ∃ out r',
      ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv4Addr.next_back r =
        Result.ok (out, r') ∧
      (out.map CidrModel.ipv4Value, RangeNext.remaining r') =
        backStep (RangeNext.remaining r) := by
  let s := CidrModel.ipv4Value r.start
  let e := CidrModel.ipv4Value r.end
  by_cases hlt : s < e
  · have hc' : compare (CidrModel.ipv4Value r.start) (CidrModel.ipv4Value r.end) =
      Ordering.lt := Nat.compare_eq_lt.mpr hlt
    rcases ipv4_sub_one_spec r.end with ⟨prev, hprev, hprevv⟩
    refine ⟨some r.end, { r with «end» := prev }, ?_, ?_⟩
    · simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv4Addr.next_back,
        Comparisons.ipv4_partial_cmp_spec, hc', hprev, core.mem.replace]
    · change (some e, RangeMath.ofInclusive s (CidrModel.ipv4Value prev)) =
        backStep (RangeMath.ofInclusive s e)
      rw [hprevv, backStep_lt s e hlt]
  · by_cases heq : s = e
    · have hc' : compare (CidrModel.ipv4Value r.start) (CidrModel.ipv4Value r.end) =
        Ordering.eq := Nat.compare_eq_eq.mpr heq
      refine ⟨some r.start, { start := RangeNext.oneAddr, «end» := RangeNext.zeroAddr }, ?_, ?_⟩
      · simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv4Addr.next_back,
          Comparisons.ipv4_partial_cmp_spec, hc', RangeNext.ipv4_replace_zero_spec,
          RangeNext.ipv4_replace_one_spec]
      · change (some s, RangeMath.ofInclusive (CidrModel.ipv4Value RangeNext.oneAddr)
          (CidrModel.ipv4Value RangeNext.zeroAddr)) = backStep (RangeMath.ofInclusive s e)
        rw [RangeNext.oneAddr_value, RangeNext.zeroAddr_value, RangeMath.sentinel_empty,
          ← heq, backStep_eq]
    · have hgt : e < s := by omega
      have hc' : compare (CidrModel.ipv4Value r.start) (CidrModel.ipv4Value r.end) =
        Ordering.gt := Nat.compare_eq_gt.mpr hgt
      refine ⟨none, r, ?_, ?_⟩
      · simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv4Addr.next_back,
          Comparisons.ipv4_partial_cmp_spec, hc']
      · change (none, RangeMath.ofInclusive s e) = backStep (RangeMath.ofInclusive s e)
        rw [backStep_gt s e hgt]
        simp [RangeMath.ofInclusive, Nat.not_le.mpr hgt]

@[expose] def firstValue : RangeMath.HalfOpen → Option Nat
  | .empty => none
  | .live lo _ => some lo

@[expose] def lastValue : RangeMath.HalfOpen → Option Nat
  | .empty => none
  | .live _ hi => some (hi - 1)

theorem range_last_spec (r : ipnet.ipext.Ipv4AddrRange) :
    ∃ out,
      ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.last r =
        Result.ok out ∧
      out.map CidrModel.ipv4Value = lastValue (RangeNext.remaining r) := by
  let s := CidrModel.ipv4Value r.start
  let e := CidrModel.ipv4Value r.end
  by_cases h : s ≤ e
  · have hc : compare s e = Ordering.lt ∨ compare s e = Ordering.eq := by
      rcases Nat.lt_or_eq_of_le h with hl | he
      · exact Or.inl (Nat.compare_eq_lt.mpr hl)
      · exact Or.inr (Nat.compare_eq_eq.mpr he)
    dsimp [s, e] at h hc
    refine ⟨some r.end, ?_, ?_⟩
    · rcases hc with hc | hc <;>
        simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.last,
          Comparisons.ipv4_partial_cmp_spec, hc]
    · simp [lastValue, RangeNext.remaining, RangeMath.ofInclusive, h]
  · have hgt : e < s := by omega
    have hc : compare s e = Ordering.gt := Nat.compare_eq_gt.mpr hgt
    dsimp [s, e] at h hc
    refine ⟨none, ?_, ?_⟩
    · simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.last,
        Comparisons.ipv4_partial_cmp_spec, hc]
    · simp [lastValue, RangeNext.remaining, RangeMath.ofInclusive, h]

theorem range_max_spec (r : ipnet.ipext.Ipv4AddrRange) :
    ∃ out,
      ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.max r =
        Result.ok out ∧
      out.map CidrModel.ipv4Value = lastValue (RangeNext.remaining r) := by
  simpa [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.max]
    using range_last_spec r

theorem range_min_spec (r : ipnet.ipext.Ipv4AddrRange) :
    ∃ out,
      ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.min r =
        Result.ok out ∧
      out.map CidrModel.ipv4Value = firstValue (RangeNext.remaining r) := by
  let s := CidrModel.ipv4Value r.start
  let e := CidrModel.ipv4Value r.end
  by_cases h : s ≤ e
  · have hc : compare s e = Ordering.lt ∨ compare s e = Ordering.eq := by
      rcases Nat.lt_or_eq_of_le h with hl | he
      · exact Or.inl (Nat.compare_eq_lt.mpr hl)
      · exact Or.inr (Nat.compare_eq_eq.mpr he)
    dsimp [s, e] at h hc
    refine ⟨some r.start, ?_, ?_⟩
    · rcases hc with hc | hc <;>
        simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.min,
          Comparisons.ipv4_partial_cmp_spec, hc]
    · simp [firstValue, RangeNext.remaining, RangeMath.ofInclusive, h]

  · have hgt : e < s := by omega
    have hc : compare s e = Ordering.gt := Nat.compare_eq_gt.mpr hgt
    dsimp [s, e] at h hc
    refine ⟨none, ?_, ?_⟩
    · simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.min,
        Comparisons.ipv4_partial_cmp_spec, hc]
    · simp [firstValue, RangeNext.remaining, RangeMath.ofInclusive, h]

private theorem u64_add_one_ok (x : U64) (h : x.val + 1 < 2^64) :
    ∃ z, (x + 1#u64 : Result U64) = Result.ok z ∧ z.val = x.val + 1 := by
  have hs : (x + 1#u64 : Result U64) ⦃ z => z.val = x.val + 1 ⦄ := by
    apply U64.add_spec
    simp only [U64.max_eq]
    norm_num at h ⊢
    omega
  cases hx : (x + 1#u64 : Result U64) with
  | ret z =>
      refine ⟨z, rfl, ?_⟩
      simpa [hx] using hs
  | vis _ _ => simp [hx] at hs
  | div => simp [hx] at hs

theorem range_count_u64_spec (r : ipnet.ipext.Ipv4AddrRange) :
    ∃ out, ipnet.ipext.Ipv4AddrRange.count_u64 r = Result.ok out ∧
      out.val = RangeMath.size (RangeNext.remaining r) := by
  let s := CidrModel.ipv4Value r.start
  let e := CidrModel.ipv4Value r.end
  by_cases hlt : s < e
  · have hc' : compare (CidrModel.ipv4Value r.start) (CidrModel.ipv4Value r.end) =
        Ordering.lt := Nat.compare_eq_lt.mpr hlt
    rcases ipv4_saturating_sub_addr_spec r.end r.start with ⟨diff, hdiff, hdiffv⟩
    have hcast : (UScalar.cast .U64 diff).val = diff.val := U32.cast_U64_val_eq diff
    have he : e < 2^32 := CidrModel.ipv4Value_bound r.end
    have hsum : (UScalar.cast .U64 diff).val + 1 < 2^64 := by
      rw [hcast, hdiffv]
      omega
    rcases u64_add_one_ok (UScalar.cast .U64 diff) hsum with ⟨out, hadd, houtv⟩
    refine ⟨out, ?_, ?_⟩
    · simp [ipnet.ipext.Ipv4AddrRange.count_u64, Comparisons.ipv4_partial_cmp_spec,
        hc', hdiff, hadd, lift, bind_ok]
    · rw [houtv, hcast, hdiffv]
      change e - s + 1 = RangeMath.size (RangeMath.ofInclusive s e)
      simp only [RangeMath.size_ofInclusive, Nat.le_of_lt hlt, ↓reduceIte]
      omega
  · by_cases heq : s = e
    · have hc' : compare (CidrModel.ipv4Value r.start) (CidrModel.ipv4Value r.end) =
          Ordering.eq := Nat.compare_eq_eq.mpr heq
      refine ⟨1#u64, ?_, ?_⟩
      · simp [ipnet.ipext.Ipv4AddrRange.count_u64,
          Comparisons.ipv4_partial_cmp_spec, hc']
      · change (1#u64).val = RangeMath.size (RangeMath.ofInclusive s e)
        simp only [RangeMath.size_ofInclusive, Nat.le_of_eq heq, ↓reduceIte]
        simp [← heq]
    · have hgt : e < s := by omega
      have hc' : compare (CidrModel.ipv4Value r.start) (CidrModel.ipv4Value r.end) =
          Ordering.gt := Nat.compare_eq_gt.mpr hgt
      refine ⟨0#u64, ?_, ?_⟩
      · simp [ipnet.ipext.Ipv4AddrRange.count_u64,
          Comparisons.ipv4_partial_cmp_spec, hc']
      · change (0#u64).val = RangeMath.size (RangeMath.ofInclusive s e)
        simp only [RangeMath.size_ofInclusive, Nat.not_le.mpr hgt, ↓reduceIte]
        rfl

private theorem usize_max_val (h64 : System.Platform.numBits = 64) :
    ipnet.core.legacy_int_modules.usize.MAX.val = 2^64 - 1 := by
  unfold ipnet.core.legacy_int_modules.usize.MAX core.num.Usize.MAX
  rw [UScalar.ofNatCore_val_eq]
  simp [Usize.max, Usize.numBits, h64]

private theorem usize_max_cast_u32 (h64 : System.Platform.numBits = 64) :
    (UScalar.cast .U32 ipnet.core.legacy_int_modules.usize.MAX).val = 2^32 - 1 := by
  rw [UScalar.cast_val_eq, usize_max_val h64]
  norm_num

private theorem usize_add_one_ok (x : Usize) (h64 : System.Platform.numBits = 64)
    (h : x.val + 1 < 2^64) :
    ∃ z, (x + 1#usize : Result Usize) = Result.ok z ∧ z.val = x.val + 1 := by
  have hs : (x + 1#usize : Result Usize) ⦃ z => z.val = x.val + 1 ⦄ := by
    apply Usize.add_spec
    rw [Usize.max]
    simp [Usize.numBits, h64]
    omega
  cases hx : (x + 1#usize : Result Usize) with
  | ret z =>
      refine ⟨z, rfl, ?_⟩
      simpa [hx] using hs
  | vis _ _ => simp [hx] at hs
  | div => simp [hx] at hs

theorem range_count_spec (r : ipnet.ipext.Ipv4AddrRange)
    (h64 : System.Platform.numBits = 64) :
    ∃ out,
      ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.count r =
        Result.ok out ∧
      out.val = RangeMath.size (RangeNext.remaining r) := by
  let s := CidrModel.ipv4Value r.start
  let e := CidrModel.ipv4Value r.end
  by_cases hlt : s < e
  · have hc' : compare (CidrModel.ipv4Value r.start) (CidrModel.ipv4Value r.end) =
        Ordering.lt := Nat.compare_eq_lt.mpr hlt
    rcases ipv4_saturating_sub_addr_spec r.end r.start with ⟨diff, hdiff, hdiffv⟩
    have hcastMax :
        (UScalar.cast .U32 ipnet.core.legacy_int_modules.usize.MAX).val = 2^32 - 1 :=
      usize_max_cast_u32 h64
    have hcond : diff ≤ UScalar.cast .U32 ipnet.core.legacy_int_modules.usize.MAX := by
      change diff.val ≤ (UScalar.cast .U32 ipnet.core.legacy_int_modules.usize.MAX).val
      rw [hcastMax]
      have hd : diff.val < 2^32 := by scalar_tac
      omega
    have hcond' : ¬ (ipnet.core.legacy_int_modules.usize.MAX.val % 4294967296 < diff.val) := by
      rw [usize_max_val h64]
      norm_num
      have hd : diff.val < 2^32 := by scalar_tac
      omega
    have hcast : (UScalar.cast .Usize diff).val = diff.val := U32.cast_Usize_val_eq diff
    have he : e < 2^32 := CidrModel.ipv4Value_bound r.end
    have hsum : (UScalar.cast .Usize diff).val + 1 < 2^64 := by
      rw [hcast, hdiffv]
      omega
    rcases usize_add_one_ok (UScalar.cast .Usize diff) h64 hsum with ⟨out, hadd, houtv⟩
    refine ⟨out, ?_, ?_⟩
    · simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.count,
        Comparisons.ipv4_partial_cmp_spec, hc', hdiff, hcond', hadd, lift, bind_ok]
    · rw [houtv, hcast, hdiffv]
      change e - s + 1 = RangeMath.size (RangeMath.ofInclusive s e)
      simp only [RangeMath.size_ofInclusive, Nat.le_of_lt hlt, ↓reduceIte]
      omega
  · by_cases heq : s = e
    · have hc' : compare (CidrModel.ipv4Value r.start) (CidrModel.ipv4Value r.end) =
          Ordering.eq := Nat.compare_eq_eq.mpr heq
      refine ⟨1#usize, ?_, ?_⟩
      · simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.count,
          Comparisons.ipv4_partial_cmp_spec, hc']
      · change (1#usize).val = RangeMath.size (RangeMath.ofInclusive s e)
        simp only [RangeMath.size_ofInclusive, Nat.le_of_eq heq, ↓reduceIte]
        simp [← heq]
    · have hgt : e < s := by omega
      have hc' : compare (CidrModel.ipv4Value r.start) (CidrModel.ipv4Value r.end) =
          Ordering.gt := Nat.compare_eq_gt.mpr hgt
      refine ⟨0#usize, ?_, ?_⟩
      · simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.count,
          Comparisons.ipv4_partial_cmp_spec, hc']
      · change (0#usize).val = RangeMath.size (RangeMath.ofInclusive s e)
        simp only [RangeMath.size_ofInclusive, Nat.not_le.mpr hgt, ↓reduceIte]
        rfl

private theorem remaining_size_bound (r : ipnet.ipext.Ipv4AddrRange) :
    RangeMath.size (RangeNext.remaining r) ≤ 2^32 := by
  let s := CidrModel.ipv4Value r.start
  let e := CidrModel.ipv4Value r.end
  have he : e < 2^32 := CidrModel.ipv4Value_bound r.end
  rw [RangeNext.remaining, RangeMath.size_ofInclusive]
  split_ifs <;> omega

theorem range_size_hint_spec (r : ipnet.ipext.Ipv4AddrRange)
    (h64 : System.Platform.numBits = 64) :
    ∃ lower upper,
      ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.size_hint r =
        Result.ok (lower, upper) ∧
      lower.val = RangeMath.size (RangeNext.remaining r) ∧
      upper = some lower := by
  rcases range_count_u64_spec r with ⟨count, hcount, hcountv⟩
  have hbound : count.val ≤ 2^32 := by rw [hcountv]; exact remaining_size_bound r
  have hmax64 :
      (UScalar.cast .U64 ipnet.core.legacy_int_modules.usize.MAX).val = 2^64 - 1 := by
    rw [UScalar.cast_val_eq, usize_max_val h64]
    norm_num
  have hnot : ¬ (count > UScalar.cast .U64 ipnet.core.legacy_int_modules.usize.MAX) := by
    change ¬ (count.val > (UScalar.cast .U64 ipnet.core.legacy_int_modules.usize.MAX).val)
    rw [hmax64]
    omega
  have hcond : count.val ≤ ipnet.core.legacy_int_modules.usize.MAX.val := by
    rw [usize_max_val h64]
    omega
  have hcast : (UScalar.cast .Usize count).val = count.val := by
    apply UScalar.cast_val_mod_pow_of_inBounds_eq
    simp [UScalarTy.numBits, h64]
    omega
  refine ⟨UScalar.cast .Usize count, some (UScalar.cast .Usize count), ?_, ?_, rfl⟩
  · simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.size_hint,
      hcount, hcond, lift, bind_ok]
  · rw [hcast, hcountv]

private theorem u64_sub_one_ok (x : U64) (h : 1 ≤ x.val) :
    ∃ z, (x - 1#u64 : Result U64) = Result.ok z ∧ z.val = x.val - 1 := by
  have hs : (x - 1#u64 : Result U64) ⦃ z => z.val = x.val - 1 ⦄ := by
    apply WP.spec_mono (U64.sub_spec (x := x) (y := 1#u64) (by simpa using h))
    intro z hz
    simpa using hz.1
  cases hx : (x - 1#u64 : Result U64) with
  | ret z =>
      refine ⟨z, rfl, ?_⟩
      simpa [hx] using hs
  | vis _ _ => simp [hx] at hs
  | div => simp [hx] at hs

private theorem usize_cast_u64_val (n : Usize) (h64 : System.Platform.numBits = 64) :
    (UScalar.cast .U64 n).val = n.val := by
  apply UScalar.cast_val_mod_pow_of_inBounds_eq
  simpa [UScalarTy.numBits, h64] using n.hBounds

@[expose] def skipFront : RangeMath.HalfOpen → Nat → Option Nat × RangeMath.HalfOpen
  | .empty, _ => (none, .empty)
  | .live lo hi, n =>
      if hi ≤ lo + n then (none, .empty)
      else if lo + n + 1 = hi then (some (lo + n), .empty)
      else (some (lo + n), .live (lo + n + 1) hi)

@[expose] def skipBack : RangeMath.HalfOpen → Nat → Option Nat × RangeMath.HalfOpen
  | .empty, _ => (none, .empty)
  | .live lo hi, n =>
      if hi ≤ lo + n then (none, .empty)
      else if lo + n + 1 = hi then (some lo, .empty)
      else (some (hi - 1 - n), .live lo (hi - 1 - n))

private theorem skipFront_empty (s e n : Nat) (h : e < s) :
    skipFront (RangeMath.ofInclusive s e) n = (none, .empty) := by
  simp [skipFront, RangeMath.ofInclusive, Nat.not_le.mpr h]

private theorem skipFront_exhausted (s e n : Nat) (h : s ≤ e)
    (hn : e + 1 ≤ s + n) :
    skipFront (RangeMath.ofInclusive s e) n = (none, .empty) := by
  simp [skipFront, RangeMath.ofInclusive, h, hn]

private theorem skipFront_last (s e n : Nat) (h : s ≤ e) (hn : s + n = e) :
    skipFront (RangeMath.ofInclusive s e) n = (some e, .empty) := by
  simp [skipFront, RangeMath.ofInclusive, h, hn]

private theorem skipFront_mid (s e n : Nat) (h : s + n < e) :
    skipFront (RangeMath.ofInclusive s e) n =
      (some (s + n), RangeMath.ofInclusive (s + n + 1) e) := by
  have hse : s ≤ e := by omega
  have hnew : s + n + 1 ≤ e := by omega
  have hnot : ¬ e + 1 ≤ s + n := by omega
  have hne : s + n ≠ e := by omega
  simp [skipFront, RangeMath.ofInclusive, hse, hnew, hnot, hne]

private theorem skipBack_empty (s e n : Nat) (h : e < s) :
    skipBack (RangeMath.ofInclusive s e) n = (none, .empty) := by
  simp [skipBack, RangeMath.ofInclusive, Nat.not_le.mpr h]

private theorem skipBack_exhausted (s e n : Nat) (h : s ≤ e)
    (hn : e + 1 ≤ s + n) :
    skipBack (RangeMath.ofInclusive s e) n = (none, .empty) := by
  simp [skipBack, RangeMath.ofInclusive, h, hn]

private theorem skipBack_last (s e n : Nat) (h : s ≤ e) (hn : s + n = e) :
    skipBack (RangeMath.ofInclusive s e) n = (some s, .empty) := by
  simp [skipBack, RangeMath.ofInclusive, h, hn]

private theorem skipBack_mid (s e n : Nat) (h : s + n < e) :
    skipBack (RangeMath.ofInclusive s e) n =
      (some (e - n), RangeMath.ofInclusive s (e - n - 1)) := by
  have hse : s ≤ e := by omega
  have hnew : s ≤ e - n - 1 := by omega
  have hnot : ¬ e + 1 ≤ s + n := by omega
  have hsub' : e - n - 1 + 1 = e - n := by omega
  simp [skipBack, RangeMath.ofInclusive, hse, hnew, hnot, hsub']
  omega

private theorem range_nth_exhausted (r : ipnet.ipext.Ipv4AddrRange) (n : Usize)
    (h64 : System.Platform.numBits = 64)
    (hn : RangeMath.size (RangeNext.remaining r) ≤ n.val) :
    ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.nth r n =
      Result.ok (none, { start := RangeNext.oneAddr, «end» := RangeNext.zeroAddr }) := by
  rcases range_count_u64_spec r with ⟨count, hcount, hcountv⟩
  have hcastn := usize_cast_u64_val n h64
  have hge : UScalar.cast .U64 n ≥ count := by
    change (UScalar.cast .U64 n).val ≥ count.val
    rw [hcastn, hcountv]
    exact hn
  have hnot : ¬ n.val < count.val := by
    rw [hcountv]
    exact Nat.not_lt.mpr hn
  simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.nth,
    hcount, hnot, RangeNext.ipv4_replace_zero_spec,
    RangeNext.ipv4_replace_one_spec, lift, bind_ok]

private theorem range_nth_back_exhausted (r : ipnet.ipext.Ipv4AddrRange) (n : Usize)
    (h64 : System.Platform.numBits = 64)
    (hn : RangeMath.size (RangeNext.remaining r) ≤ n.val) :
    ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv4Addr.nth_back r n =
      Result.ok (none, { start := RangeNext.oneAddr, «end» := RangeNext.zeroAddr }) := by
  rcases range_count_u64_spec r with ⟨count, hcount, hcountv⟩
  have hcastn := usize_cast_u64_val n h64
  have hge : UScalar.cast .U64 n ≥ count := by
    change (UScalar.cast .U64 n).val ≥ count.val
    rw [hcastn, hcountv]
    exact hn
  have hnot : ¬ n.val < count.val := by
    rw [hcountv]
    exact Nat.not_lt.mpr hn
  simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv4Addr.nth_back,
    hcount, hnot, RangeNext.ipv4_replace_zero_spec,
    RangeNext.ipv4_replace_one_spec, lift, bind_ok]

theorem range_nth_spec (r : ipnet.ipext.Ipv4AddrRange) (n : Usize)
    (h64 : System.Platform.numBits = 64) :
    ∃ out r',
      ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.nth r n =
        Result.ok (out, r') ∧
      (out.map CidrModel.ipv4Value, RangeNext.remaining r') =
        skipFront (RangeNext.remaining r) n.val := by
  let s := CidrModel.ipv4Value r.start
  let e := CidrModel.ipv4Value r.end
  let L := RangeMath.size (RangeNext.remaining r)
  by_cases hex : L ≤ n.val
  · refine ⟨none, { start := RangeNext.oneAddr, «end» := RangeNext.zeroAddr },
      range_nth_exhausted r n h64 hex, ?_⟩
    rw [RangeNext.remaining, RangeNext.oneAddr_value, RangeNext.zeroAddr_value,
      RangeMath.sentinel_empty]
    by_cases hse : s ≤ e
    · have hlen : L = e + 1 - s := by
        simp only [L, RangeNext.remaining, RangeMath.size_ofInclusive]
        dsimp [s, e] at hse ⊢
        simp [hse]
      have hn : e + 1 ≤ s + n.val := by omega
      change (none, .empty) = skipFront (RangeMath.ofInclusive s e) n.val
      rw [skipFront_exhausted s e n.val hse hn]
    · have hgt : e < s := by omega
      change (none, .empty) = skipFront (RangeMath.ofInclusive s e) n.val
      rw [skipFront_empty s e n.val hgt]
  · have hlt : n.val < L := by omega
    have hse : s ≤ e := by
      by_contra hn
      have hzero : L = 0 := by
        simp only [L, RangeNext.remaining, RangeMath.size_ofInclusive]
        dsimp [s, e] at hn ⊢
        simp [hn]
      omega
    have hlen : L = e + 1 - s := by
      simp only [L, RangeNext.remaining, RangeMath.size_ofInclusive]
      dsimp [s, e] at hse ⊢
      simp [hse]
    have hsum : s + n.val ≤ e := by omega
    rcases range_count_u64_spec r with ⟨count, hcount, hcountv⟩
    have hcastn := usize_cast_u64_val n h64
    have hltCount : n.val < count.val := by rw [hcountv]; exact hlt
    have hcountpos : 1 ≤ count.val := by omega
    rcases u64_sub_one_ok count hcountpos with ⟨lastIndex, hsub, hsubv⟩
    by_cases hlast : s + n.val = e
    · have heqIndex : UScalar.cast .U64 n = lastIndex :=
        UScalar.eq_of_val_eq (by
          rw [hcastn, hsubv, hcountv]
          change n.val = L - 1
          rw [hlen]
          omega)
      have hiLt : lastIndex.val < count.val := by omega
      refine ⟨some r.end, { start := RangeNext.oneAddr, «end» := RangeNext.zeroAddr }, ?_, ?_⟩
      · simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.nth,
          hcount, hsub, heqIndex, hiLt, RangeNext.ipv4_replace_zero_spec,
          RangeNext.ipv4_replace_one_spec, lift, bind_ok]
      · change (some e, RangeMath.ofInclusive (CidrModel.ipv4Value RangeNext.oneAddr)
          (CidrModel.ipv4Value RangeNext.zeroAddr)) =
          skipFront (RangeMath.ofInclusive s e) n.val
        rw [RangeNext.oneAddr_value, RangeNext.zeroAddr_value,
          RangeMath.sentinel_empty, skipFront_last s e n.val hse hlast]
    · have hmid : s + n.val < e := by omega
      have hneIndex : UScalar.cast .U64 n ≠ lastIndex := by
        intro h
        have hv := congrArg UScalar.val h
        rw [hcastn, hsubv, hcountv] at hv
        change n.val = L - 1 at hv
        rw [hlen] at hv
        omega
      let n32 := UScalar.cast .U32 (UScalar.cast .U64 n)
      have hn32 : n32.val = n.val := by
        dsimp [n32]
        rw [UScalar.cast_val_mod_pow_of_inBounds_eq, hcastn]
        rw [hlen] at hlt
        have he : e < 2^32 := CidrModel.ipv4Value_bound r.end
        simp
        omega
      rcases RangeNext.ipv4_saturating_add_spec r.start n32 with ⟨nth, hnth, hnthv⟩
      have he : e < 2^32 := CidrModel.ipv4Value_bound r.end
      have hnthval : CidrModel.ipv4Value nth = s + n.val := by
        rw [hnthv, hn32]
        simp
        omega
      rcases RangeNext.ipv4_add_one_spec nth with ⟨next, hnext, hnextv⟩
      have hnextval : CidrModel.ipv4Value next = s + n.val + 1 := by
        rw [hnextv, hnthval]
        simp
        omega
      refine ⟨some nth, { r with start := next }, ?_, ?_⟩
      · simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.nth,
          hcount, hltCount, hsub, hneIndex, hnth, hnext, n32, lift, bind_ok]
      · change (some (CidrModel.ipv4Value nth),
          RangeMath.ofInclusive (CidrModel.ipv4Value next) e) =
          skipFront (RangeMath.ofInclusive s e) n.val
        rw [hnthval, hnextval, skipFront_mid s e n.val hmid]

theorem range_nth_back_spec (r : ipnet.ipext.Ipv4AddrRange) (n : Usize)
    (h64 : System.Platform.numBits = 64) :
    ∃ out r',
      ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv4Addr.nth_back r n =
        Result.ok (out, r') ∧
      (out.map CidrModel.ipv4Value, RangeNext.remaining r') =
        skipBack (RangeNext.remaining r) n.val := by
  let s := CidrModel.ipv4Value r.start
  let e := CidrModel.ipv4Value r.end
  let L := RangeMath.size (RangeNext.remaining r)
  by_cases hex : L ≤ n.val
  · refine ⟨none, { start := RangeNext.oneAddr, «end» := RangeNext.zeroAddr },
      range_nth_back_exhausted r n h64 hex, ?_⟩
    rw [RangeNext.remaining, RangeNext.oneAddr_value, RangeNext.zeroAddr_value,
      RangeMath.sentinel_empty]
    by_cases hse : s ≤ e
    · have hlen : L = e + 1 - s := by
        simp only [L, RangeNext.remaining, RangeMath.size_ofInclusive]
        dsimp [s, e] at hse ⊢
        simp [hse]
      have hn : e + 1 ≤ s + n.val := by omega
      change (none, .empty) = skipBack (RangeMath.ofInclusive s e) n.val
      rw [skipBack_exhausted s e n.val hse hn]
    · have hgt : e < s := by omega
      change (none, .empty) = skipBack (RangeMath.ofInclusive s e) n.val
      rw [skipBack_empty s e n.val hgt]
  · have hlt : n.val < L := by omega
    have hse : s ≤ e := by
      by_contra hn
      have hzero : L = 0 := by
        simp only [L, RangeNext.remaining, RangeMath.size_ofInclusive]
        dsimp [s, e] at hn ⊢
        simp [hn]
      omega
    have hlen : L = e + 1 - s := by
      simp only [L, RangeNext.remaining, RangeMath.size_ofInclusive]
      dsimp [s, e] at hse ⊢
      simp [hse]
    have hsum : s + n.val ≤ e := by omega
    rcases range_count_u64_spec r with ⟨count, hcount, hcountv⟩
    have hcastn := usize_cast_u64_val n h64
    have hltCount : n.val < count.val := by rw [hcountv]; exact hlt
    have hcountpos : 1 ≤ count.val := by omega
    rcases u64_sub_one_ok count hcountpos with ⟨lastIndex, hsub, hsubv⟩
    by_cases hlast : s + n.val = e
    · have heqIndex : UScalar.cast .U64 n = lastIndex :=
        UScalar.eq_of_val_eq (by
          rw [hcastn, hsubv, hcountv]
          change n.val = L - 1
          rw [hlen]
          omega)
      have hiLt : lastIndex.val < count.val := by omega
      refine ⟨some r.start, { start := RangeNext.oneAddr, «end» := RangeNext.zeroAddr }, ?_, ?_⟩
      · simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv4Addr.nth_back,
          hcount, hsub, heqIndex, hiLt, RangeNext.ipv4_replace_zero_spec,
          RangeNext.ipv4_replace_one_spec, lift, bind_ok]
      · change (some s, RangeMath.ofInclusive (CidrModel.ipv4Value RangeNext.oneAddr)
          (CidrModel.ipv4Value RangeNext.zeroAddr)) =
          skipBack (RangeMath.ofInclusive s e) n.val
        rw [RangeNext.oneAddr_value, RangeNext.zeroAddr_value,
          RangeMath.sentinel_empty, skipBack_last s e n.val hse hlast]
    · have hmid : s + n.val < e := by omega
      have hneIndex : UScalar.cast .U64 n ≠ lastIndex := by
        intro h
        have hv := congrArg UScalar.val h
        rw [hcastn, hsubv, hcountv] at hv
        change n.val = L - 1 at hv
        rw [hlen] at hv
        omega
      let n32 := UScalar.cast .U32 (UScalar.cast .U64 n)
      have hn32 : n32.val = n.val := by
        dsimp [n32]
        rw [UScalar.cast_val_mod_pow_of_inBounds_eq, hcastn]
        rw [hlen] at hlt
        have he : e < 2^32 := CidrModel.ipv4Value_bound r.end
        simp
        omega
      rcases ipv4_saturating_sub_spec r.end n32 with ⟨nth, hnth, hnthv⟩
      have hnthval : CidrModel.ipv4Value nth = e - n.val := by
        rw [hnthv, hn32]
      rcases ipv4_sub_one_spec nth with ⟨prev, hprev, hprevv⟩
      have hprevval : CidrModel.ipv4Value prev = e - n.val - 1 := by
        rw [hprevv, hnthval]
      refine ⟨some nth, { r with «end» := prev }, ?_, ?_⟩
      · simp [ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv4Addr.nth_back,
          hcount, hltCount, hsub, hneIndex, hnth, hprev, n32, lift, bind_ok]
      · change (some (CidrModel.ipv4Value nth),
          RangeMath.ofInclusive s (CidrModel.ipv4Value prev)) =
          skipBack (RangeMath.ofInclusive s e) n.val
        rw [hnthval, hprevval, skipBack_mid s e n.val hmid]

/-- Every selected front/back step preserves abstract exhaustion, for any raw
    representation of an empty IPv4 range and any 64-bit skip count. -/
theorem range_empty_no_revival (r : ipnet.ipext.Ipv4AddrRange) (n : Usize)
    (h64 : System.Platform.numBits = 64)
    (hempty : RangeNext.remaining r = .empty) :
    (∃ r', ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.next r =
        Result.ok (none, r') ∧ RangeNext.remaining r' = .empty) ∧
    (∃ r', ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv4Addr.next_back r =
        Result.ok (none, r') ∧ RangeNext.remaining r' = .empty) ∧
    (∃ r', ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.nth r n =
        Result.ok (none, r') ∧ RangeNext.remaining r' = .empty) ∧
    (∃ r', ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv4Addr.nth_back r n =
        Result.ok (none, r') ∧ RangeNext.remaining r' = .empty) := by
  rcases RangeNext.range_next_spec r with ⟨outF, rF, hF, hvF⟩
  rcases range_next_back_spec r with ⟨outB, rB, hB, hvB⟩
  rcases range_nth_spec r n h64 with ⟨outN, rN, hN, hvN⟩
  rcases range_nth_back_spec r n h64 with ⟨outNB, rNB, hNB, hvNB⟩
  rw [hempty] at hvF hvB hvN hvNB
  simp [RangeMath.next, backStep, skipFront, skipBack] at hvF hvB hvN hvNB
  have hnoneF : outF = none := by cases outF <;> simp_all
  have hnoneB : outB = none := by cases outB <;> simp_all
  have hnoneN : outN = none := by cases outN <;> simp_all
  have hnoneNB : outNB = none := by cases outNB <;> simp_all
  exact ⟨⟨rF, hnoneF ▸ hF, hvF.2⟩,
    ⟨rB, hnoneB ▸ hB, hvB.2⟩,
    ⟨rN, hnoneN ▸ hN, hvN.2⟩,
    ⟨rNB, hnoneNB ▸ hNB, hvNB.2⟩⟩

end RangeMore
