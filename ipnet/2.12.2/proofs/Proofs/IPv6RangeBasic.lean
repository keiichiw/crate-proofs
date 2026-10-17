module
public import Proofs.IPv6RangeMath
public import Proofs.IPv6AddressEq
public import Proofs.IPv6ConstructorMath
public import Proofs.Comparisons

public section

namespace IPv6RangeBasic

open Aeneas Aeneas.Std Result

@[expose] def lastValue (s e : Nat) : Option Nat :=
  if s ≤ e then some e else none

@[expose] def firstValue (s e : Nat) : Option Nat :=
  if s ≤ e then some s else none

/-- The selected `last` body uses the independent numeric order. -/
theorem last_spec (r : ipnet.ipext.Ipv6AddrRange) :
    ∃ out,
      ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.last r =
        Result.ok out ∧
      out.map CidrModel.ipv6Value =
        lastValue (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end) := by
  let s := CidrModel.ipv6Value r.start
  let e := CidrModel.ipv6Value r.end
  by_cases h : s ≤ e
  · have hc : compare s e = Ordering.lt ∨ compare s e = Ordering.eq := by
      rcases Nat.lt_or_eq_of_le h with hl | he
      · exact Or.inl (Nat.compare_eq_lt.mpr hl)
      · exact Or.inr (Nat.compare_eq_eq.mpr he)
    dsimp [s, e] at h hc
    refine ⟨some r.end, ?_, ?_⟩
    · rcases hc with hc | hc <;>
        simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.last,
          Comparisons.ipv6_partial_cmp_spec, hc]
    · simp [lastValue, h]
  · have hgt : e < s := by omega
    have hc : compare s e = Ordering.gt := Nat.compare_eq_gt.mpr hgt
    dsimp [s, e] at h hc
    refine ⟨none, ?_, ?_⟩
    · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.last,
        Comparisons.ipv6_partial_cmp_spec, hc]
    · simp [lastValue, h]

theorem max_spec (r : ipnet.ipext.Ipv6AddrRange) :
    ∃ out,
      ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.max r =
        Result.ok out ∧
      out.map CidrModel.ipv6Value =
        lastValue (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end) := by
  simpa [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.max]
    using last_spec r

theorem min_spec (r : ipnet.ipext.Ipv6AddrRange) :
    ∃ out,
      ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.min r =
        Result.ok out ∧
      out.map CidrModel.ipv6Value =
        firstValue (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end) := by
  let s := CidrModel.ipv6Value r.start
  let e := CidrModel.ipv6Value r.end
  by_cases h : s ≤ e
  · have hc : compare s e = Ordering.lt ∨ compare s e = Ordering.eq := by
      rcases Nat.lt_or_eq_of_le h with hl | he
      · exact Or.inl (Nat.compare_eq_lt.mpr hl)
      · exact Or.inr (Nat.compare_eq_eq.mpr he)
    dsimp [s, e] at h hc
    refine ⟨some r.start, ?_, ?_⟩
    · rcases hc with hc | hc <;>
        simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.min,
          Comparisons.ipv6_partial_cmp_spec, hc]
    · simp [firstValue, h]
  · have hgt : e < s := by omega
    have hc : compare s e = Ordering.gt := Nat.compare_eq_gt.mpr hgt
    dsimp [s, e] at h hc
    refine ⟨none, ?_, ?_⟩
    · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.min,
        Comparisons.ipv6_partial_cmp_spec, hc]
    · simp [firstValue, h]

/-- The exact numeric result of the selected IPv6 address subtraction body. -/
theorem ipv6_saturating_sub_addr_spec
    (a b : ipnet.core.net.ip_addr.Ipv6Addr) :
    ∃ out,
      ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpSubIpv6AddrU128.saturating_sub a b =
        Result.ok out ∧
      out.val = CidrModel.ipv6Value a - CidrModel.ipv6Value b := by
  rcases AddressConversions.ipv6_into_u128_spec a with ⟨x, hx, hxv⟩
  rcases AddressConversions.ipv6_into_u128_spec b with ⟨y, hy, hyv⟩
  refine ⟨core.num.U128.saturating_sub x y, ?_, ?_⟩
  · simp [ipnet.core.net.ip_addr.Ipv6Addr.Insts.IpnetIpextIpSubIpv6AddrU128.saturating_sub,
      core.convert.IntoFrom.into, hx, hy, lift, bind_ok]
  · rw [core.num.U128.saturating_sub_val, hxv, hyv]

private theorem u128_add_one_ok (x : U128) (h : x.val + 1 < 2 ^ 128) :
    ∃ z, (x + 1#u128 : Result U128) = Result.ok z ∧ z.val = x.val + 1 := by
  have hs : (x + 1#u128 : Result U128) ⦃ z => z.val = x.val + 1 ⦄ := by
    apply U128.add_spec
    norm_num [U128.max_eq]
    omega
  cases hx : (x + 1#u128 : Result U128) with
  | ret z =>
      refine ⟨z, rfl, ?_⟩
      simpa [hx] using hs
  | vis _ _ => simp [hx] at hs
  | div => simp [hx] at hs

/-- The unique full raw IPv6 range overflows the private U128 count. -/
theorem count_u128_full_fail (r : ipnet.ipext.Ipv6AddrRange)
    (hfull : CidrModel.ipv6Value r.start = 0 ∧
      CidrModel.ipv6Value r.end = IPv6RangeMath.maxAddress) :
    ipnet.ipext.Ipv6AddrRange.count_u128 r = Result.fail .integerOverflow := by
  let s := CidrModel.ipv6Value r.start
  let e := CidrModel.ipv6Value r.end
  have hlt : s < e := by
    rcases hfull with ⟨hs, he⟩
    dsimp [s, e]
    rw [hs, he]
    norm_num [IPv6RangeMath.maxAddress, IPv6RangeMath.limit]
  have hc : compare s e = Ordering.lt := Nat.compare_eq_lt.mpr hlt
  rcases ipv6_saturating_sub_addr_spec r.end r.start with ⟨diff, hdiff, hdiffv⟩
  have hd : diff.val = 2 ^ 128 - 1 := by
    rw [hdiffv, hfull.1, hfull.2]
    rfl
  have hadd : (diff + 1#u128 : Result U128) = Result.fail .integerOverflow :=
    U128.add_one_max_fail diff hd
  dsimp [s, e] at hc
  simp [ipnet.ipext.Ipv6AddrRange.count_u128,
    Comparisons.ipv6_partial_cmp_spec, hc, hdiff, hadd, bind_ok]

/-- Every other raw IPv6 range has an exact private U128 count. -/
theorem count_u128_normal (r : ipnet.ipext.Ipv6AddrRange)
    (hnot : ¬ (CidrModel.ipv6Value r.start = 0 ∧
      CidrModel.ipv6Value r.end = IPv6RangeMath.maxAddress)) :
    ∃ out, ipnet.ipext.Ipv6AddrRange.count_u128 r = Result.ok out ∧
      out.val = IPv6RangeMath.card
        (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end) := by
  let s := CidrModel.ipv6Value r.start
  let e := CidrModel.ipv6Value r.end
  by_cases hlt : s < e
  · have hc : compare s e = Ordering.lt := Nat.compare_eq_lt.mpr hlt
    rcases ipv6_saturating_sub_addr_spec r.end r.start with ⟨diff, hdiff, hdiffv⟩
    have hlt128 : diff.val + 1 < 2 ^ 128 := by
      rw [hdiffv]
      have hs : s < IPv6RangeMath.limit := CidrModel.ipv6Value_bound r.start
      have he : e < IPv6RangeMath.limit := CidrModel.ipv6Value_bound r.end
      have hcard := IPv6RangeMath.card_eq_limit_iff_full s e hs he
      have hn : IPv6RangeMath.card s e ≠ IPv6RangeMath.limit := by
        intro h
        exact hnot (hcard.mp h)
      have hc' : IPv6RangeMath.card s e = e + 1 - s :=
        IPv6RangeMath.card_live s e (by omega)
      have hle := IPv6RangeMath.card_le_limit s e hs he
      rw [hc'] at hn hle
      simp [IPv6RangeMath.limit] at hn hle
      omega
    rcases u128_add_one_ok diff hlt128 with ⟨out, hadd, houtv⟩
    refine ⟨out, ?_, ?_⟩
    · dsimp [s, e] at hc
      simp [ipnet.ipext.Ipv6AddrRange.count_u128,
        Comparisons.ipv6_partial_cmp_spec, hc, hdiff, hadd, bind_ok]
    · rw [houtv, hdiffv]
      change e - s + 1 = IPv6RangeMath.card s e
      rw [IPv6RangeMath.card_live s e (by omega)]
      omega
  · by_cases heq : s = e
    · have hc : compare s e = Ordering.eq := Nat.compare_eq_eq.mpr heq
      refine ⟨1#u128, ?_, ?_⟩
      · dsimp [s, e] at hc
        simp [ipnet.ipext.Ipv6AddrRange.count_u128,
          Comparisons.ipv6_partial_cmp_spec, hc]
      · change 1 = IPv6RangeMath.card s e
        rw [IPv6RangeMath.card_live s e (by omega)]
        omega
    · have hgt : e < s := by omega
      have hc : compare s e = Ordering.gt := Nat.compare_eq_gt.mpr hgt
      refine ⟨0#u128, ?_, ?_⟩
      · dsimp [s, e] at hc
        simp [ipnet.ipext.Ipv6AddrRange.count_u128,
          Comparisons.ipv6_partial_cmp_spec, hc]
      · change 0 = IPv6RangeMath.card s e
        rw [IPv6RangeMath.card_empty s e hgt]

private theorem ipv6_ne_value (a b : ipnet.core.net.ip_addr.Ipv6Addr) :
    ∃ out,
      core.cmp.PartialEq.ne.trait_default
        ipnet.core.net.ip_addr.Ipv6Addr.Insts.CoreCmpPartialEqIpv6Addr a b = Result.ok out ∧
      (out ↔ CidrModel.ipv6Value a ≠ CidrModel.ipv6Value b) := by
  rcases IPv6AddressEq.ipv6_eq_bool a b with ⟨eqb, heq, heqv⟩
  have heqwp :
      ipnet.core.net.ip_addr.Ipv6Addr.Insts.CoreCmpPartialEqIpv6Addr.eq a b
        ⦃ q => q ↔ a = b ⦄ := by
    rw [heq]
    simpa only [WP.spec_ok] using heqv
  have hne := core.cmp.PartialEq.ne.trait_default.spec
    ipnet.core.net.ip_addr.Ipv6Addr.Insts.CoreCmpPartialEqIpv6Addr a b heqwp
  cases hr : core.cmp.PartialEq.ne.trait_default
      ipnet.core.net.ip_addr.Ipv6Addr.Insts.CoreCmpPartialEqIpv6Addr a b with
  | ret z =>
      refine ⟨z, rfl, ?_⟩
      have hz : z ↔ a ≠ b := by simpa [hr] using hne
      exact hz.trans (not_congr (IPv6AddressEq.ipv6Value_eq_iff a b).symm)
  | vis _ _ => simp [hr] at hne
  | div => simp [hr] at hne

/-- The extracted gate permits U128 counting exactly when the raw range is not
    the unique full IPv6 interval. -/
theorem can_count_u128_spec (r : ipnet.ipext.Ipv6AddrRange) :
    ∃ out, ipnet.ipext.Ipv6AddrRange.can_count_u128 r = Result.ok out ∧
      (out ↔ IPv6RangeMath.card
        (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end) <
        IPv6RangeMath.limit) := by
  rcases IPv6ConstructorMath.ipv6_new_zero_spec with ⟨zero, hzero, hzv⟩
  rcases IPv6ConstructorMath.ipv6_new_max_spec with ⟨max, hmax, hmv⟩
  rcases ipv6_ne_value r.start zero with ⟨b0, hb0, hb0v⟩
  by_cases hs : CidrModel.ipv6Value r.start = 0
  · have hb : b0 = false := by
      cases b0 <;> simp_all
    rcases ipv6_ne_value r.end max with ⟨b1, hb1, hb1v⟩
    refine ⟨b1, ?_, ?_⟩
    · simp [ipnet.ipext.Ipv6AddrRange.can_count_u128,
        hzero, hb0, hb, hmax, hb1, bind_ok]
    · have hsc : CidrModel.ipv6Value r.start < IPv6RangeMath.limit :=
        CidrModel.ipv6Value_bound r.start
      have hec : CidrModel.ipv6Value r.end < IPv6RangeMath.limit :=
        CidrModel.ipv6Value_bound r.end
      have hiff := IPv6RangeMath.card_eq_limit_iff_full
        (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end) hsc hec
      have hle := IPv6RangeMath.card_le_limit
        (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end) hsc hec
      rw [hmv] at hb1v
      change b1 ↔ CidrModel.ipv6Value r.end ≠ IPv6RangeMath.maxAddress at hb1v
      constructor
      · intro hb1t
        have hne := hb1v.mp hb1t
        omega
      · intro hlt
        apply hb1v.mpr
        intro heq
        have hfull : IPv6RangeMath.card
            (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end) =
            IPv6RangeMath.limit := hiff.mpr ⟨hs, heq⟩
        omega
  · have hb : b0 = true := by
      cases b0 <;> simp_all
    refine ⟨true, ?_, ?_⟩
    · simp [ipnet.ipext.Ipv6AddrRange.can_count_u128,
        hzero, hb0, hb, bind_ok]
    · have hsc : CidrModel.ipv6Value r.start < IPv6RangeMath.limit :=
        CidrModel.ipv6Value_bound r.start
      have hec : CidrModel.ipv6Value r.end < IPv6RangeMath.limit :=
        CidrModel.ipv6Value_bound r.end
      have hiff := IPv6RangeMath.card_eq_limit_iff_full
        (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end) hsc hec
      have hle := IPv6RangeMath.card_le_limit
        (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end) hsc hec
      constructor
      · intro _
        by_contra hnotlt
        have hc : IPv6RangeMath.card
            (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end) =
            IPv6RangeMath.limit := by omega
        exact hs (hiff.mp hc).1
      · intro _
        trivial

private theorem usize_max_val (h64 : System.Platform.numBits = 64) :
    ipnet.core.legacy_int_modules.usize.MAX.val = IPv6RangeMath.usizeMax := by
  unfold ipnet.core.legacy_int_modules.usize.MAX core.num.Usize.MAX
  rw [UScalar.ofNatCore_val_eq]
  simp [Usize.max, Usize.numBits, h64, IPv6RangeMath.usizeMax,
    IPv6RangeMath.usizeLimit]

private theorem usize_max_cast_u128 (h64 : System.Platform.numBits = 64) :
    (UScalar.cast .U128 ipnet.core.legacy_int_modules.usize.MAX).val =
      IPv6RangeMath.usizeMax := by
  have hb : ipnet.core.legacy_int_modules.usize.MAX.val <
      2 ^ UScalarTy.U128.numBits := by
    rw [usize_max_val h64]
    norm_num [IPv6RangeMath.usizeMax, IPv6RangeMath.usizeLimit,
      UScalarTy.numBits]
  rw [UScalar.cast_val_mod_pow_of_inBounds_eq .U128 _ hb,
    usize_max_val h64]

/-- The selected public `count` body returns the exact cardinality whenever it
    fits the pinned 64-bit Usize. -/
theorem count_normal_spec (r : ipnet.ipext.Ipv6AddrRange)
    (h64 : System.Platform.numBits = 64)
    (hfit : IPv6RangeMath.card
      (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end) ≤
      IPv6RangeMath.usizeMax) :
    ∃ out,
      ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.count r =
        Result.ok out ∧
      out.val = IPv6RangeMath.card
        (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end) := by
  have hnot : ¬ (CidrModel.ipv6Value r.start = 0 ∧
      CidrModel.ipv6Value r.end = IPv6RangeMath.maxAddress) := by
    intro hf
    have hs : CidrModel.ipv6Value r.start < IPv6RangeMath.limit :=
      CidrModel.ipv6Value_bound r.start
    have he : CidrModel.ipv6Value r.end < IPv6RangeMath.limit :=
      CidrModel.ipv6Value_bound r.end
    have hc := (IPv6RangeMath.card_eq_limit_iff_full _ _ hs he).mpr hf
    have hl := IPv6RangeMath.usize_limit_lt_limit
    have hsmall : IPv6RangeMath.usizeMax < IPv6RangeMath.limit := by
      simp only [IPv6RangeMath.usizeMax]
      omega
    omega
  rcases count_u128_normal r hnot with ⟨count, hcount, hval⟩
  have hcmp : count ≤ UScalar.cast .U128 ipnet.core.legacy_int_modules.usize.MAX := by
    change count.val ≤ (UScalar.cast .U128 ipnet.core.legacy_int_modules.usize.MAX).val
    rw [usize_max_cast_u128 h64, hval]
    exact hfit
  have hcast : (UScalar.cast .Usize count).val = count.val := by
    apply UScalar.cast_val_mod_pow_of_inBounds_eq
    simp [UScalarTy.numBits, h64]
    rw [hval]
    have : IPv6RangeMath.usizeMax < 2^64 := by
      norm_num [IPv6RangeMath.usizeMax, IPv6RangeMath.usizeLimit]
    omega
  have hcond : ¬ ipnet.core.legacy_int_modules.usize.MAX.val % 2^128 < count.val := by
    rw [Nat.mod_eq_of_lt]
    · rw [usize_max_val h64, hval]
      exact Nat.not_lt.mpr hfit
    · rw [usize_max_val h64]
      norm_num [IPv6RangeMath.usizeMax, IPv6RangeMath.usizeLimit]
  norm_num at hcond
  refine ⟨UScalar.cast .Usize count, ?_, ?_⟩
  · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.count,
      hcount, hcond, lift, bind_ok]
  · rw [hcast, hval]

/-- On the pinned 64-bit target, the selected public `count` fails precisely
    when the independent cardinality exceeds Usize. -/
theorem count_overflow_spec (r : ipnet.ipext.Ipv6AddrRange)
    (h64 : System.Platform.numBits = 64)
    (hbig : IPv6RangeMath.usizeMax < IPv6RangeMath.card
      (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end)) :
    ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.count r =
      Result.fail .integerOverflow := by
  by_cases hfull : CidrModel.ipv6Value r.start = 0 ∧
      CidrModel.ipv6Value r.end = IPv6RangeMath.maxAddress
  · have hcount := count_u128_full_fail r hfull
    simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.count,
      hcount]
  · rcases count_u128_normal r hfull with ⟨count, hcount, hval⟩
    have hcmp : ¬ count ≤ UScalar.cast .U128 ipnet.core.legacy_int_modules.usize.MAX := by
      change ¬ count.val ≤
        (UScalar.cast .U128 ipnet.core.legacy_int_modules.usize.MAX).val
      rw [usize_max_cast_u128 h64, hval]
      omega
    have hcond : ipnet.core.legacy_int_modules.usize.MAX.val % 2^128 < count.val := by
      rw [Nat.mod_eq_of_lt]
      · rw [usize_max_val h64, hval]
        exact hbig
      · rw [usize_max_val h64]
        norm_num [IPv6RangeMath.usizeMax, IPv6RangeMath.usizeLimit]
    norm_num at hcond
    have hadd : (ipnet.core.legacy_int_modules.usize.MAX + 1#usize : Result Usize) =
        Result.fail .integerOverflow := by
      apply Usize.add_one_max_fail
      rw [usize_max_val h64]
      simp [IPv6RangeMath.usizeMax, IPv6RangeMath.usizeLimit,
        Usize.numBits, h64]
    simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.count,
      hcount, hcond, hadd, lift, bind_ok]

/-- Full raw-state classification of the selected public count on the pinned
    64-bit target, including the 2^128-element range. -/
theorem count_spec (r : ipnet.ipext.Ipv6AddrRange)
    (h64 : System.Platform.numBits = 64) :
    (IPv6RangeMath.card (CidrModel.ipv6Value r.start)
        (CidrModel.ipv6Value r.end) ≤ IPv6RangeMath.usizeMax →
      ∃ out,
        ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.count r =
          Result.ok out ∧
        out.val = IPv6RangeMath.card
          (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end)) ∧
    (IPv6RangeMath.usizeMax < IPv6RangeMath.card
        (CidrModel.ipv6Value r.start) (CidrModel.ipv6Value r.end) →
      ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.count r =
        Result.fail .integerOverflow) := by
  exact ⟨count_normal_spec r h64, count_overflow_spec r h64⟩

end IPv6RangeBasic
