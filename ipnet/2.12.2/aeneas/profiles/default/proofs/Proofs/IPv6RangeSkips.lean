module
public import Proofs.IPv6RangeSteps
public section

open Aeneas Aeneas.Std Result

namespace IPv6RangeSkips

private theorem usize_cast_u128_val (n : Usize)
    (h64 : System.Platform.numBits = 64) :
    (UScalar.cast .U128 n).val = n.val := by
  apply UScalar.cast_val_mod_pow_of_inBounds_eq
  simp [UScalarTy.numBits]
  have hn : n.val < 2^64 := by simpa [Usize.numBits, h64] using UScalar.hBounds n
  omega

private theorem u128_sub_one_ok (x : U128) (h : 1 ≤ x.val) :
    ∃ z, (x - 1#u128 : Result U128) = Result.ok z ∧ z.val = x.val - 1 := by
  have hs : (x - 1#u128 : Result U128) ⦃ z => z.val = x.val - 1 ⦄ := by
    apply WP.spec_mono (U128.sub_spec (x := x) (y := 1#u128) (by simpa using h))
    intro z hz
    simpa using hz.1
  cases hx : (x - 1#u128 : Result U128) with
  | ret z =>
      refine ⟨z, rfl, ?_⟩
      simpa [hx] using hs
  | vis _ _ => simp [hx] at hs
  | div => simp [hx] at hs

private theorem usize_max_val (h64 : System.Platform.numBits = 64) :
    ipnet.core.legacy_int_modules.usize.MAX.val = 2^64 - 1 := by
  unfold ipnet.core.legacy_int_modules.usize.MAX core.num.Usize.MAX
  rw [UScalar.ofNatCore_val_eq]
  simp [Usize.max, Usize.numBits, h64]

private theorem usize_max_cast_u128 (h64 : System.Platform.numBits = 64) :
    (UScalar.cast .U128 ipnet.core.legacy_int_modules.usize.MAX).val = 2^64 - 1 := by
  rw [UScalar.cast_val_eq, usize_max_val h64]
  norm_num

private theorem u128_cast_usize_val (x : U128)
    (h64 : System.Platform.numBits = 64) (h : x.val ≤ 2^64 - 1) :
    (UScalar.cast .Usize x).val = x.val := by
  apply UScalar.cast_val_mod_pow_of_inBounds_eq
  simp [UScalarTy.numBits, h64]
  omega

/-- The actual size_hint returns an exact upper bound only when the Nat
    cardinality fits usize; it remains normally successful for the full space. -/
theorem size_hint_spec (r : ipnet.ipext.Ipv6AddrRange)
    (h64 : System.Platform.numBits = 64) :
    ∃ lower upper,
      ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.size_hint r =
        Result.ok (lower, upper) ∧
      (lower.val, upper.map UScalar.val) =
        IPv6RangeMath.sizeHint (CidrModel.ipv6Value r.start)
          (CidrModel.ipv6Value r.end) := by
  let s := CidrModel.ipv6Value r.start
  let e := CidrModel.ipv6Value r.end
  let c := IPv6RangeMath.card s e
  have hs : s < IPv6RangeMath.limit := CidrModel.ipv6Value_bound r.start
  have he : e < IPv6RangeMath.limit := CidrModel.ipv6Value_bound r.end
  rcases IPv6RangeBasic.can_count_u128_spec r with ⟨b, hb, hbiff⟩
  have hmax := usize_max_val h64
  have hmax128 := usize_max_cast_u128 h64
  by_cases hsmall128 : c < IPv6RangeMath.limit
  · have hbt : b = true := hbiff.mpr hsmall128
    have hnotfull : ¬ (s = 0 ∧ e = IPv6RangeMath.maxAddress) := by
      intro hf
      have hc := (IPv6RangeMath.card_eq_limit_iff_full s e hs he).mpr hf
      omega
    rcases IPv6RangeBasic.count_u128_normal r hnotfull with ⟨count, hcount, hcountv⟩
    by_cases hbig : IPv6RangeMath.usizeMax < c
    · have hbigNat : 2^64 - 1 < c := by
        simpa [IPv6RangeMath.usizeMax, IPv6RangeMath.usizeLimit] using hbig
      have hcond : ipnet.core.legacy_int_modules.usize.MAX.val % 2^128 < count.val := by
        rw [hmax, hcountv]
        norm_num
        exact hbigNat
      norm_num at hcond
      refine ⟨ipnet.core.legacy_int_modules.usize.MAX, none, ?_, ?_⟩
      · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.size_hint,
          hb, hbt, hcount, hcond, lift, bind_ok]
      · change (ipnet.core.legacy_int_modules.usize.MAX.val, none) =
          IPv6RangeMath.sizeHint s e
        rw [IPv6RangeMath.sizeHint_overflow s e hbig, hmax]
        simp [IPv6RangeMath.usizeMax, IPv6RangeMath.usizeLimit]
    · have hfit : c ≤ IPv6RangeMath.usizeMax := by omega
      have hfitNat : c ≤ 2^64 - 1 := by
        simpa [IPv6RangeMath.usizeMax, IPv6RangeMath.usizeLimit] using hfit
      have hcond : ¬ (ipnet.core.legacy_int_modules.usize.MAX.val % 2^128 < count.val) := by
        rw [hmax, hcountv]
        norm_num
        omega
      norm_num at hcond
      have hcast : (UScalar.cast .Usize count).val = c := by
        rw [u128_cast_usize_val count h64 (by rw [hcountv]; exact hfitNat), hcountv]
      refine ⟨UScalar.cast .Usize count, some (UScalar.cast .Usize count), ?_, ?_⟩
      · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.size_hint,
          hb, hbt, hcount, hcond, lift, bind_ok]
      · rw [IPv6RangeMath.sizeHint_exact s e hfit]
        simp [hcast, c]
  · have hbf : b = false := by
      cases b with
      | false => rfl
      | true => exact False.elim (hsmall128 (hbiff.mp rfl))
    have hcard : c = IPv6RangeMath.limit := by
      have hle := IPv6RangeMath.card_le_limit s e hs he
      omega
    have hbig : IPv6RangeMath.usizeMax < c := by
      rw [hcard]
      norm_num [IPv6RangeMath.usizeMax, IPv6RangeMath.limit,
        IPv6RangeMath.usizeLimit]
    refine ⟨ipnet.core.legacy_int_modules.usize.MAX, none, ?_, ?_⟩
    · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.size_hint,
        hb, hbf]
    · rw [IPv6RangeMath.sizeHint_overflow s e hbig]
      simp [IPv6RangeMath.usizeMax, IPv6RangeMath.usizeLimit, hmax]

/-- The selected `nth` body returns the exact indexed address and stores the
    exact numeric raw endpoints from the independent Nat model. -/
theorem nth_spec (r : ipnet.ipext.Ipv6AddrRange) (n : Usize)
    (h64 : System.Platform.numBits = 64) :
    ∃ out r',
      ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.nth r n =
        Result.ok (out, r') ∧
      (out.map CidrModel.ipv6Value,
        CidrModel.ipv6Value r'.start, CidrModel.ipv6Value r'.end) =
        IPv6RangeMath.nth (CidrModel.ipv6Value r.start)
          (CidrModel.ipv6Value r.end) n.val := by
  let s := CidrModel.ipv6Value r.start
  let e := CidrModel.ipv6Value r.end
  let c := IPv6RangeMath.card s e
  have hs : s < IPv6RangeMath.limit := CidrModel.ipv6Value_bound r.start
  have he : e < IPv6RangeMath.limit := CidrModel.ipv6Value_bound r.end
  have hn128 : (UScalar.cast .U128 n).val = n.val := usize_cast_u128_val n h64
  have hnBound : n.val < 2^64 := by
    simpa [Usize.numBits, h64] using UScalar.hBounds n
  rcases IPv6RangeBasic.can_count_u128_spec r with ⟨b, hb, hbiff⟩
  by_cases hsmall : c < IPv6RangeMath.limit
  · have hbt : b = true := hbiff.mpr hsmall
    have hnotfull : ¬ (s = 0 ∧ e = IPv6RangeMath.maxAddress) := by
      intro hf
      have hc := (IPv6RangeMath.card_eq_limit_iff_full s e hs he).mpr hf
      omega
    rcases IPv6RangeBasic.count_u128_normal r hnotfull with ⟨count, hcount, hcountv⟩
    have hcountC : count.val = c := hcountv
    by_cases hex : c ≤ n.val
    · have hge : UScalar.cast .U128 n ≥ count := by
        change (UScalar.cast .U128 n).val ≥ count.val
        rw [hn128, hcountv]
        exact hex
      rcases IPv6RangeSteps.ipv6_replace_zero_spec r.end with ⟨zero, hzero, hzv⟩
      rcases IPv6RangeSteps.ipv6_replace_one_spec r.start with ⟨one, hone, hov⟩
      refine ⟨none, { start := one, «end» := zero }, ?_, ?_⟩
      · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.nth,
          hb, hbt, hcount, hzero, hone, lift, bind_ok]
        intro hltRaw
        have hmod : n.val % 340282366920938463463374607431768211456 = n.val := by
          apply Nat.mod_eq_of_lt
          omega
        rw [hmod, hcountC] at hltRaw
        omega
      · change (none, CidrModel.ipv6Value one, CidrModel.ipv6Value zero) =
          IPv6RangeMath.nth s e n.val
        rw [hov, hzv, IPv6RangeMath.nth_out_of_bounds s e n.val hex]
    · have hlt : n.val < c := by omega
      have hse : s ≤ e := by
        by_contra hn
        have hzero : c = 0 := IPv6RangeMath.card_empty s e (by omega)
        omega
      have hcard : c = e + 1 - s := IPv6RangeMath.card_live s e hse
      have hltLen : n.val < e + 1 - s := by simpa [hcard] using hlt
      have hsum : s + n.val ≤ e := by omega
      have hltCount : UScalar.cast .U128 n < count := by
        change (UScalar.cast .U128 n).val < count.val
        rw [hn128, hcountv]
        exact hlt
      have hcountpos : 1 ≤ count.val := by rw [hcountC]; omega
      rcases u128_sub_one_ok count hcountpos with ⟨lastIndex, hsub, hsubv⟩
      by_cases hlast : n.val + 1 = c
      · have heqIndex : UScalar.cast .U128 n = lastIndex :=
          UScalar.eq_of_val_eq (by
            rw [hn128, hsubv, hcountC]
            omega)
        have hlastIndexLt : lastIndex.val < count.val := by omega
        rcases IPv6RangeSteps.ipv6_replace_zero_spec r.end with ⟨zero, hzero, hzv⟩
        rcases IPv6RangeSteps.ipv6_replace_one_spec r.start with ⟨one, hone, hov⟩
        refine ⟨some r.end, { start := one, «end» := zero }, ?_, ?_⟩
        · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.nth,
            hb, hbt, hcount, hsub, heqIndex, hzero, hone, lift, bind_ok]
          exact hlastIndexLt
        · change (some e, CidrModel.ipv6Value one, CidrModel.ipv6Value zero) =
            IPv6RangeMath.nth s e n.val
          rw [hov, hzv]
          have hlaste : n.val + 1 = IPv6RangeMath.card s e := hlast
          rw [IPv6RangeMath.nth_last s e n.val hlaste]
      · have hmid : n.val + 1 < c := by omega
        have hmidLen : n.val + 1 < e + 1 - s := by simpa [hcard] using hmid
        have hneIndex : UScalar.cast .U128 n ≠ lastIndex := by
          intro hh
          have hv := congrArg UScalar.val hh
          rw [hn128, hsubv, hcountC] at hv
          omega
        rcases IPv6RangeSteps.ipv6_saturating_add_spec r.start (UScalar.cast .U128 n) with
          ⟨nth, hnth, hnthv⟩
        have hnthval : CidrModel.ipv6Value nth = s + n.val := by
          rw [hnthv, hn128]
          have he' : e ≤ 2^128 - 1 := by simp [IPv6RangeMath.limit] at he; omega
          change min (s + n.val) (2^128 - 1) = s + n.val
          exact Nat.min_eq_left (by omega)
        rcases IPv6RangeSteps.ipv6_add_one_spec nth with ⟨next, hnext, hnextv⟩
        have hnextval : CidrModel.ipv6Value next = s + n.val + 1 := by
          rw [hnextv, hnthval]
          have he' : e ≤ 2^128 - 1 := by simp [IPv6RangeMath.limit] at he; omega
          change min (s + n.val + 1) (2^128 - 1) = s + n.val + 1
          exact Nat.min_eq_left (by omega)
        refine ⟨some nth, { r with start := next }, ?_, ?_⟩
        · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.nth,
            hb, hbt, hcount, hsub, hneIndex, hnth, hnext, lift, bind_ok]
          intro hgeRaw
          have hmod : n.val % 340282366920938463463374607431768211456 = n.val := by
            apply Nat.mod_eq_of_lt
            omega
          rw [hmod, hcountC] at hgeRaw
          omega
        · change (some (CidrModel.ipv6Value nth), CidrModel.ipv6Value next, e) =
            IPv6RangeMath.nth s e n.val
          rw [hnthval, hnextval, IPv6RangeMath.nth_middle s e n.val hmid]
  · have hcard : c = IPv6RangeMath.limit := by
      have hle := IPv6RangeMath.card_le_limit s e hs he
      omega
    have hfull : s = 0 ∧ e = IPv6RangeMath.maxAddress :=
      (IPv6RangeMath.card_eq_limit_iff_full s e hs he).mp hcard
    have hbf : b = false := by
      cases b with
      | false => rfl
      | true => exact False.elim (hsmall (hbiff.mp rfl))
    rcases IPv6RangeSteps.ipv6_saturating_add_spec r.start (UScalar.cast .U128 n) with
      ⟨nth, hnth, hnthv⟩
    have hnthval : CidrModel.ipv6Value nth = n.val := by
      rw [hnthv, hn128]
      change min (s + n.val) (2^128 - 1) = n.val
      rw [hfull.1]
      have hle : n.val ≤ 2^128 - 1 := by omega
      simpa using Nat.min_eq_left hle
    rcases IPv6RangeSteps.ipv6_add_one_spec nth with ⟨next, hnext, hnextv⟩
    have hnextval : CidrModel.ipv6Value next = n.val + 1 := by
      rw [hnextv, hnthval]
      have hle : n.val + 1 ≤ 2^128 - 1 := by omega
      change min (n.val + 1) (2^128 - 1) = n.val + 1
      exact Nat.min_eq_left hle
    refine ⟨some nth, { r with start := next }, ?_, ?_⟩
    · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.nth,
        hb, hbf, hnth, hnext, lift, bind_ok]
    · change (some (CidrModel.ipv6Value nth), CidrModel.ipv6Value next, e) =
        IPv6RangeMath.nth s e n.val
      rw [hnthval, hnextval, hfull.1, hfull.2]
      rw [IPv6RangeMath.nth_full n.val (by simpa [IPv6RangeMath.usizeLimit] using hnBound)]

/-- The selected `nth_back` body returns the exact reverse indexed address
    and stores the exact numeric raw endpoints, including on the full space. -/
theorem nth_back_spec (r : ipnet.ipext.Ipv6AddrRange) (n : Usize)
    (h64 : System.Platform.numBits = 64) :
    ∃ out r',
      ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv6Addr.nth_back r n =
        Result.ok (out, r') ∧
      (out.map CidrModel.ipv6Value,
        CidrModel.ipv6Value r'.start, CidrModel.ipv6Value r'.end) =
        IPv6RangeMath.nthBack (CidrModel.ipv6Value r.start)
          (CidrModel.ipv6Value r.end) n.val := by
  let s := CidrModel.ipv6Value r.start
  let e := CidrModel.ipv6Value r.end
  let c := IPv6RangeMath.card s e
  have hs : s < IPv6RangeMath.limit := CidrModel.ipv6Value_bound r.start
  have he : e < IPv6RangeMath.limit := CidrModel.ipv6Value_bound r.end
  have hn128 : (UScalar.cast .U128 n).val = n.val := usize_cast_u128_val n h64
  have hnBound : n.val < 2^64 := by
    simpa [Usize.numBits, h64] using UScalar.hBounds n
  rcases IPv6RangeBasic.can_count_u128_spec r with ⟨b, hb, hbiff⟩
  by_cases hsmall : c < IPv6RangeMath.limit
  · have hbt : b = true := hbiff.mpr hsmall
    have hnotfull : ¬ (s = 0 ∧ e = IPv6RangeMath.maxAddress) := by
      intro hf
      have hc := (IPv6RangeMath.card_eq_limit_iff_full s e hs he).mpr hf
      omega
    rcases IPv6RangeBasic.count_u128_normal r hnotfull with ⟨count, hcount, hcountv⟩
    have hcountC : count.val = c := hcountv
    by_cases hex : c ≤ n.val
    · rcases IPv6RangeSteps.ipv6_replace_zero_spec r.end with ⟨zero, hzero, hzv⟩
      rcases IPv6RangeSteps.ipv6_replace_one_spec r.start with ⟨one, hone, hov⟩
      refine ⟨none, { start := one, «end» := zero }, ?_, ?_⟩
      · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv6Addr.nth_back,
          hb, hbt, hcount, hzero, hone, lift, bind_ok]
        intro hltRaw
        have hmod : n.val % 340282366920938463463374607431768211456 = n.val := by
          apply Nat.mod_eq_of_lt
          omega
        rw [hmod, hcountC] at hltRaw
        omega
      · change (none, CidrModel.ipv6Value one, CidrModel.ipv6Value zero) =
          IPv6RangeMath.nthBack s e n.val
        rw [hov, hzv, IPv6RangeMath.nthBack_out_of_bounds s e n.val hex]
    · have hlt : n.val < c := by omega
      have hse : s ≤ e := by
        by_contra hn
        have hzero : c = 0 := IPv6RangeMath.card_empty s e (by omega)
        omega
      have hcard : c = e + 1 - s := IPv6RangeMath.card_live s e hse
      have hltLen : n.val < e + 1 - s := by simpa [hcard] using hlt
      have hsum : s + n.val ≤ e := by omega
      have hcountpos : 1 ≤ count.val := by rw [hcountC]; omega
      rcases u128_sub_one_ok count hcountpos with ⟨lastIndex, hsub, hsubv⟩
      by_cases hlast : n.val + 1 = c
      · have heqIndex : UScalar.cast .U128 n = lastIndex :=
          UScalar.eq_of_val_eq (by rw [hn128, hsubv, hcountC]; omega)
        have hlastIndexLt : lastIndex.val < count.val := by omega
        rcases IPv6RangeSteps.ipv6_replace_zero_spec r.end with ⟨zero, hzero, hzv⟩
        rcases IPv6RangeSteps.ipv6_replace_one_spec r.start with ⟨one, hone, hov⟩
        refine ⟨some r.start, { start := one, «end» := zero }, ?_, ?_⟩
        · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv6Addr.nth_back,
            hb, hbt, hcount, hsub, heqIndex, hzero, hone, lift, bind_ok]
          exact hlastIndexLt
        · change (some s, CidrModel.ipv6Value one, CidrModel.ipv6Value zero) =
            IPv6RangeMath.nthBack s e n.val
          rw [hov, hzv, IPv6RangeMath.nthBack_last s e n.val hlast]
      · have hmid : n.val + 1 < c := by omega
        have hmidLen : n.val + 1 < e + 1 - s := by simpa [hcard] using hmid
        have hneIndex : UScalar.cast .U128 n ≠ lastIndex := by
          intro hh
          have hv := congrArg UScalar.val hh
          rw [hn128, hsubv, hcountC] at hv
          omega
        rcases IPv6RangeSteps.ipv6_saturating_sub_spec r.end (UScalar.cast .U128 n) with
          ⟨nth, hnth, hnthv⟩
        have hnthval : CidrModel.ipv6Value nth = e - n.val := by
          rw [hnthv, hn128]
        rcases IPv6RangeSteps.ipv6_sub_one_spec nth with ⟨prev, hprev, hprevv⟩
        have hprevval : CidrModel.ipv6Value prev = e - n.val - 1 := by
          rw [hprevv, hnthval]
        refine ⟨some nth, { r with «end» := prev }, ?_, ?_⟩
        · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv6Addr.nth_back,
            hb, hbt, hcount, hsub, hneIndex, hnth, hprev, lift, bind_ok]
          intro hgeRaw
          have hmod : n.val % 340282366920938463463374607431768211456 = n.val := by
            apply Nat.mod_eq_of_lt
            omega
          rw [hmod, hcountC] at hgeRaw
          omega
        · change (some (CidrModel.ipv6Value nth), s, CidrModel.ipv6Value prev) =
            IPv6RangeMath.nthBack s e n.val
          rw [hnthval, hprevval, IPv6RangeMath.nthBack_middle s e n.val hmid]
  · have hcard : c = IPv6RangeMath.limit := by
      have hle := IPv6RangeMath.card_le_limit s e hs he
      omega
    have hfull : s = 0 ∧ e = IPv6RangeMath.maxAddress :=
      (IPv6RangeMath.card_eq_limit_iff_full s e hs he).mp hcard
    have hbf : b = false := by
      cases b with
      | false => rfl
      | true => exact False.elim (hsmall (hbiff.mp rfl))
    rcases IPv6RangeSteps.ipv6_saturating_sub_spec r.end (UScalar.cast .U128 n) with
      ⟨nth, hnth, hnthv⟩
    have hnthval : CidrModel.ipv6Value nth = e - n.val := by
      rw [hnthv, hn128]
    rcases IPv6RangeSteps.ipv6_sub_one_spec nth with ⟨prev, hprev, hprevv⟩
    have hprevval : CidrModel.ipv6Value prev = e - n.val - 1 := by
      rw [hprevv, hnthval]
    refine ⟨some nth, { r with «end» := prev }, ?_, ?_⟩
    · simp [ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv6Addr.nth_back,
        hb, hbf, hnth, hprev, lift, bind_ok]
    · change (some (CidrModel.ipv6Value nth), s, CidrModel.ipv6Value prev) =
        IPv6RangeMath.nthBack s e n.val
      rw [hnthval, hprevval, hfull.1, hfull.2]
      rw [IPv6RangeMath.nthBack_full n.val
        (by simpa [IPv6RangeMath.usizeLimit] using hnBound)]

private theorem nth_to_skipFront (s e n : Nat) :
    (let (o, a, b) := IPv6RangeMath.nth s e n
     (o, RangeMath.ofInclusive a b)) =
      RangeMore.skipFront (RangeMath.ofInclusive s e) n := by
  by_cases hse : s ≤ e
  · by_cases hex : IPv6RangeMath.card s e ≤ n
    · have hn : e + 1 ≤ s + n := by
        rw [IPv6RangeMath.card_live s e hse] at hex
        omega
      rw [IPv6RangeMath.nth_out_of_bounds s e n hex]
      simp [RangeMore.skipFront, RangeMath.ofInclusive,
        hse, hn]
    · by_cases hlast : n + 1 = IPv6RangeMath.card s e
      · have heq : s + n = e := by
          rw [IPv6RangeMath.card_live s e hse] at hlast
          omega
        rw [IPv6RangeMath.nth_last s e n hlast]
        simp [RangeMore.skipFront, RangeMath.ofInclusive,
          hse, heq]
      · have hmid : n + 1 < IPv6RangeMath.card s e := by omega
        have hlt : s + n < e := by
          rw [IPv6RangeMath.card_live s e hse] at hmid
          omega
        have hnew : s + n + 1 ≤ e := by omega
        have hnot : ¬ e + 1 ≤ s + n := by omega
        have hne : s + n ≠ e := by omega
        rw [IPv6RangeMath.nth_middle s e n hmid]
        simp [RangeMore.skipFront, RangeMath.ofInclusive, hse, hnew, hnot, hne]
  · have hgt : e < s := by omega
    have hex : IPv6RangeMath.card s e ≤ n := by
      rw [IPv6RangeMath.card_empty s e hgt]
      omega
    rw [IPv6RangeMath.nth_out_of_bounds s e n hex]
    simp [RangeMore.skipFront, RangeMath.ofInclusive,
      Nat.not_le.mpr hgt]

private theorem nthBack_to_skipBack (s e n : Nat) :
    (let (o, a, b) := IPv6RangeMath.nthBack s e n
     (o, RangeMath.ofInclusive a b)) =
      RangeMore.skipBack (RangeMath.ofInclusive s e) n := by
  by_cases hse : s ≤ e
  · by_cases hex : IPv6RangeMath.card s e ≤ n
    · have hn : e + 1 ≤ s + n := by
        rw [IPv6RangeMath.card_live s e hse] at hex
        omega
      rw [IPv6RangeMath.nthBack_out_of_bounds s e n hex]
      simp [RangeMore.skipBack, RangeMath.ofInclusive,
        hse, hn]
    · by_cases hlast : n + 1 = IPv6RangeMath.card s e
      · have heq : s + n = e := by
          rw [IPv6RangeMath.card_live s e hse] at hlast
          omega
        rw [IPv6RangeMath.nthBack_last s e n hlast]
        simp [RangeMore.skipBack, RangeMath.ofInclusive,
          hse, heq]
      · have hmid : n + 1 < IPv6RangeMath.card s e := by omega
        have hlt : s + n < e := by
          rw [IPv6RangeMath.card_live s e hse] at hmid
          omega
        have hnew : s ≤ e - n - 1 := by omega
        have hnot : ¬ e + 1 ≤ s + n := by omega
        have hne : s + n ≠ e := by omega
        rw [IPv6RangeMath.nthBack_middle s e n hmid]
        simp [RangeMore.skipBack, RangeMath.ofInclusive, hse, hnew, hnot, hne]
        omega
  · have hgt : e < s := by omega
    have hex : IPv6RangeMath.card s e ≤ n := by
      rw [IPv6RangeMath.card_empty s e hgt]
      omega
    rw [IPv6RangeMath.nthBack_out_of_bounds s e n hex]
    simp [RangeMore.skipBack, RangeMath.ofInclusive,
      Nat.not_le.mpr hgt]

/-- Half-open remaining-state form of the checked `nth` body contract. -/
theorem nth_remaining_spec (r : ipnet.ipext.Ipv6AddrRange) (n : Usize)
    (h64 : System.Platform.numBits = 64) :
    ∃ out r',
      ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.nth r n =
        Result.ok (out, r') ∧
      (out.map CidrModel.ipv6Value, IPv6RangeSteps.remaining r') =
        RangeMore.skipFront (IPv6RangeSteps.remaining r) n.val := by
  rcases nth_spec r n h64 with ⟨out, r', hr, hv⟩
  refine ⟨out, r', hr, ?_⟩
  have hm := congrArg
    (fun triple : Option Nat × Nat × Nat =>
      let (o, a, b) := triple
      (o, RangeMath.ofInclusive a b)) hv
  simpa [IPv6RangeSteps.remaining, IPv6RangeMath.remaining] using
    hm.trans (nth_to_skipFront (CidrModel.ipv6Value r.start)
      (CidrModel.ipv6Value r.end) n.val)

/-- Half-open remaining-state form of the checked `nth_back` body contract. -/
theorem nth_back_remaining_spec (r : ipnet.ipext.Ipv6AddrRange) (n : Usize)
    (h64 : System.Platform.numBits = 64) :
    ∃ out r',
      ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv6Addr.nth_back r n =
        Result.ok (out, r') ∧
      (out.map CidrModel.ipv6Value, IPv6RangeSteps.remaining r') =
        RangeMore.skipBack (IPv6RangeSteps.remaining r) n.val := by
  rcases nth_back_spec r n h64 with ⟨out, r', hr, hv⟩
  refine ⟨out, r', hr, ?_⟩
  have hm := congrArg
    (fun triple : Option Nat × Nat × Nat =>
      let (o, a, b) := triple
      (o, RangeMath.ofInclusive a b)) hv
  simpa [IPv6RangeSteps.remaining, IPv6RangeMath.remaining] using
    hm.trans (nthBack_to_skipBack (CidrModel.ipv6Value r.start)
      (CidrModel.ipv6Value r.end) n.val)

/-- Every selected front/back/skip operation preserves abstract exhaustion,
    even when the concrete empty state is not the canonical `(1,0)` sentinel. -/
theorem range_empty_no_revival (r : ipnet.ipext.Ipv6AddrRange) (n : Usize)
    (h64 : System.Platform.numBits = 64)
    (hempty : IPv6RangeSteps.remaining r = .empty) :
    (∃ r',
      ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.next r =
        Result.ok (none, r') ∧ IPv6RangeSteps.remaining r' = .empty) ∧
    (∃ r',
      ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv6Addr.next_back r =
        Result.ok (none, r') ∧ IPv6RangeSteps.remaining r' = .empty) ∧
    (∃ r',
      ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.nth r n =
        Result.ok (none, r') ∧ IPv6RangeSteps.remaining r' = .empty) ∧
    (∃ r',
      ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv6Addr.nth_back r n =
        Result.ok (none, r') ∧ IPv6RangeSteps.remaining r' = .empty) := by
  rcases IPv6RangeSteps.range_next_spec r with ⟨outF, rF, hF, hvF⟩
  rcases IPv6RangeSteps.range_next_back_spec r with ⟨outB, rB, hB, hvB⟩
  rcases nth_remaining_spec r n h64 with ⟨outN, rN, hN, hvN⟩
  rcases nth_back_remaining_spec r n h64 with ⟨outNB, rNB, hNB, hvNB⟩
  rw [hempty] at hvF hvB hvN hvNB
  simp [RangeMath.next, RangeMore.backStep, RangeMore.skipFront,
    RangeMore.skipBack] at hvF hvB hvN hvNB
  cases outF <;> cases outB <;> cases outN <;> cases outNB <;>
    simp_all

/-- The four selected ways to advance an IPv6 address range. -/
inductive EmptyOperation where
  | next
  | nextBack
  | nth (n : Usize)
  | nthBack (n : Usize)

/-- Exact actual calls in a finite sequence after exhaustion; each returned
    option is `none`. -/
inductive EmptyCalls : List EmptyOperation → ipnet.ipext.Ipv6AddrRange →
    ipnet.ipext.Ipv6AddrRange → Prop where
  | nil (r) : EmptyCalls [] r r
  | next {ops r r' r''}
      (hcall : ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.next r =
        Result.ok (none, r'))
      (hrest : EmptyCalls ops r' r'') :
      EmptyCalls (EmptyOperation.next :: ops) r r''
  | nextBack {ops r r' r''}
      (hcall : ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv6Addr.next_back r =
        Result.ok (none, r'))
      (hrest : EmptyCalls ops r' r'') :
      EmptyCalls (EmptyOperation.nextBack :: ops) r r''
  | nth {ops r r' r'' n}
      (hcall : ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.nth r n =
        Result.ok (none, r'))
      (hrest : EmptyCalls ops r' r'') :
      EmptyCalls (EmptyOperation.nth n :: ops) r r''
  | nthBack {ops r r' r'' n}
      (hcall : ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv6Addr.nth_back r n =
        Result.ok (none, r'))
      (hrest : EmptyCalls ops r' r'') :
      EmptyCalls (EmptyOperation.nthBack n :: ops) r r''

/-- Any finite mixed sequence of actual selected calls after exhaustion
    returns only `none` and leaves the independent remaining set empty. -/
theorem finite_mixed_no_revival (ops : List EmptyOperation)
    (r : ipnet.ipext.Ipv6AddrRange) (h64 : System.Platform.numBits = 64)
    (hempty : IPv6RangeSteps.remaining r = .empty) :
    ∃ r', EmptyCalls ops r r' ∧ IPv6RangeSteps.remaining r' = .empty := by
  induction ops generalizing r with
  | nil => exact ⟨r, EmptyCalls.nil r, hempty⟩
  | cons op tail ih =>
    cases op with
    | next =>
        rcases (range_empty_no_revival r 0#usize h64 hempty).1 with
          ⟨r₁, hcall, h₁⟩
        rcases ih r₁ h₁ with ⟨r₂, hrest, h₂⟩
        exact ⟨r₂, EmptyCalls.next hcall hrest, h₂⟩
    | nextBack =>
        rcases (range_empty_no_revival r 0#usize h64 hempty).2.1 with
          ⟨r₁, hcall, h₁⟩
        rcases ih r₁ h₁ with ⟨r₂, hrest, h₂⟩
        exact ⟨r₂, EmptyCalls.nextBack hcall hrest, h₂⟩
    | nth n =>
        rcases (range_empty_no_revival r n h64 hempty).2.2.1 with
          ⟨r₁, hcall, h₁⟩
        rcases ih r₁ h₁ with ⟨r₂, hrest, h₂⟩
        exact ⟨r₂, EmptyCalls.nth hcall hrest, h₂⟩
    | nthBack n =>
        rcases (range_empty_no_revival r n h64 hempty).2.2.2 with
          ⟨r₁, hcall, h₁⟩
        rcases ih r₁ h₁ with ⟨r₂, hrest, h₂⟩
        exact ⟨r₂, EmptyCalls.nthBack hcall hrest, h₂⟩

end IPv6RangeSkips
