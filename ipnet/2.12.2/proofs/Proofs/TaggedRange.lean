module
public import Proofs.RangeMore
public import Proofs.IPv6RangeSkips
public import Proofs.IPv6RangeBasic

public section

namespace TaggedRange

open Aeneas Aeneas.Std Result

private theorem map_v4 (o : Option ipnet.core.net.ip_addr.Ipv4Addr) :
    core.option.Option.map ipnet.P.Insts.CoreOpsFunctionFnOnceTupleIpv4AddrIpAddr o
      ipnet.core.net.ip_addr.IpAddr.V4.constructor =
      Result.ok (o.map ipnet.core.net.ip_addr.IpAddr.V4) := by
  cases o <;>
    simp [core.option.Option.map,
      ipnet.P.Insts.CoreOpsFunctionFnOnceTupleIpv4AddrIpAddr.call_once,
      ipnet.core.net.ip_addr.IpAddr.V4.constructor]

private theorem map_v6 (o : Option ipnet.core.net.ip_addr.Ipv6Addr) :
    core.option.Option.map ipnet.P.Insts.CoreOpsFunctionFnOnceTupleIpv6AddrIpAddr o
      ipnet.core.net.ip_addr.IpAddr.V6.constructor =
      Result.ok (o.map ipnet.core.net.ip_addr.IpAddr.V6) := by
  cases o <;>
    simp [core.option.Option.map,
      ipnet.P.Insts.CoreOpsFunctionFnOnceTupleIpv6AddrIpAddr.call_once,
      ipnet.core.net.ip_addr.IpAddr.V6.constructor]

@[expose] def addrValue : ipnet.core.net.ip_addr.IpAddr → Nat
  | .V4 a => CidrModel.ipv4Value a
  | .V6 a => CidrModel.ipv6Value a

@[expose] def remaining : ipnet.ipext.IpAddrRange → RangeMath.HalfOpen
  | .V4 r => RangeNext.remaining r
  | .V6 r => IPv6RangeSteps.remaining r

@[expose] def family : ipnet.ipext.IpAddrRange → Bool
  | .V4 _ => false
  | .V6 _ => true

@[expose] def addrFamily : ipnet.core.net.ip_addr.IpAddr → Bool
  | .V4 _ => false
  | .V6 _ => true

/-- Both tagged branches forward the exact concrete step and its raw updated
    state, while their numeric observation is the independent interval step. -/
theorem next_spec (r : ipnet.ipext.IpAddrRange) :
    ∃ out r',
      ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.next r =
        Result.ok (out, r') ∧
      (out.map addrValue, remaining r') = RangeMath.next (remaining r) ∧
      family r' = family r ∧
      (∀ a, out = some a → addrFamily a = family r) ∧
      (match r with
       | .V4 a => ∃ o a',
           ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.next a =
             Result.ok (o, a') ∧
           out = o.map ipnet.core.net.ip_addr.IpAddr.V4 ∧ r' = .V4 a'
       | .V6 a => ∃ o a',
           ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.next a =
             Result.ok (o, a') ∧
           out = o.map ipnet.core.net.ip_addr.IpAddr.V6 ∧ r' = .V6 a') := by
  cases r with
  | V4 a =>
      rcases RangeNext.range_next_spec a with ⟨o, a', hnext, hmath⟩
      refine ⟨o.map ipnet.core.net.ip_addr.IpAddr.V4, .V4 a', ?_, ?_, rfl, ?_, ?_⟩
      · simp [ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.next,
          hnext, map_v4]
      · simpa [remaining, addrValue, Option.map_map, Function.comp_def] using hmath
      · intro x hx
        cases o with
        | none => simp at hx
        | some y =>
            simp only [Option.map_some] at hx
            cases hx
            rfl
      · exact ⟨o, a', hnext, rfl, rfl⟩
  | V6 a =>
      rcases IPv6RangeSteps.range_next_spec a with ⟨o, a', hnext, hmath⟩
      refine ⟨o.map ipnet.core.net.ip_addr.IpAddr.V6, .V6 a', ?_, ?_, rfl, ?_, ?_⟩
      · simp [ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.next,
          hnext, map_v6]
      · simpa [remaining, addrValue, Option.map_map, Function.comp_def] using hmath
      · intro x hx
        cases o with
        | none => simp at hx
        | some y =>
            simp only [Option.map_some] at hx
            cases hx
            rfl
      · exact ⟨o, a', hnext, rfl, rfl⟩

private theorem v6_last_value (r : ipnet.ipext.Ipv6AddrRange) :
    IPv6RangeBasic.lastValue (CidrModel.ipv6Value r.start)
      (CidrModel.ipv6Value r.end) =
      RangeMore.lastValue (IPv6RangeSteps.remaining r) := by
  unfold IPv6RangeBasic.lastValue RangeMore.lastValue IPv6RangeSteps.remaining
  by_cases h : CidrModel.ipv6Value r.start ≤ CidrModel.ipv6Value r.end <;>
    simp [IPv6RangeMath.remaining, RangeMath.ofInclusive, h]

private theorem v6_first_value (r : ipnet.ipext.Ipv6AddrRange) :
    IPv6RangeBasic.firstValue (CidrModel.ipv6Value r.start)
      (CidrModel.ipv6Value r.end) =
      RangeMore.firstValue (IPv6RangeSteps.remaining r) := by
  unfold IPv6RangeBasic.firstValue RangeMore.firstValue IPv6RangeSteps.remaining
  by_cases h : CidrModel.ipv6Value r.start ≤ CidrModel.ipv6Value r.end <;>
    simp [IPv6RangeMath.remaining, RangeMath.ofInclusive, h]

/-- The selected tagged `last` forwards the exact concrete address and keeps
    its family while observing the endpoint of the independent interval. -/
theorem last_spec (r : ipnet.ipext.IpAddrRange) :
    ∃ out,
      ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.last r =
        Result.ok out ∧
      out.map addrValue = RangeMore.lastValue (remaining r) ∧
      (∀ a, out = some a → addrFamily a = family r) ∧
      (match r with
       | .V4 a => ∃ o,
           ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.last a =
             Result.ok o ∧ out = o.map ipnet.core.net.ip_addr.IpAddr.V4
       | .V6 a => ∃ o,
           ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.last a =
             Result.ok o ∧ out = o.map ipnet.core.net.ip_addr.IpAddr.V6) := by
  cases r with
  | V4 a =>
      rcases RangeMore.range_last_spec a with ⟨o, ho, hvalue⟩
      refine ⟨o.map ipnet.core.net.ip_addr.IpAddr.V4, ?_, ?_, ?_, ?_⟩
      · simp [ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.last,
          ho, map_v4]
      · simpa [remaining, addrValue, Option.map_map, Function.comp_def] using hvalue
      · intro x hx
        cases o with
        | none => simp at hx
        | some y =>
            simp only [Option.map_some] at hx
            cases hx
            rfl
      · exact ⟨o, ho, rfl⟩
  | V6 a =>
      rcases IPv6RangeBasic.last_spec a with ⟨o, ho, hvalue⟩
      refine ⟨o.map ipnet.core.net.ip_addr.IpAddr.V6, ?_, ?_, ?_, ?_⟩
      · simp [ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.last,
          ho, map_v6]
      · rw [v6_last_value] at hvalue
        simpa [remaining, addrValue, Option.map_map, Function.comp_def] using hvalue
      · intro x hx
        cases o with
        | none => simp at hx
        | some y =>
            simp only [Option.map_some] at hx
            cases hx
            rfl
      · exact ⟨o, ho, rfl⟩
/-- The selected tagged `max` forwards the exact concrete address and keeps
    its family while observing the endpoint of the independent interval. -/
theorem max_spec (r : ipnet.ipext.IpAddrRange) :
    ∃ out,
      ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.max r =
        Result.ok out ∧
      out.map addrValue = RangeMore.lastValue (remaining r) ∧
      (∀ a, out = some a → addrFamily a = family r) ∧
      (match r with
       | .V4 a => ∃ o,
           ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.max a =
             Result.ok o ∧ out = o.map ipnet.core.net.ip_addr.IpAddr.V4
       | .V6 a => ∃ o,
           ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.max a =
             Result.ok o ∧ out = o.map ipnet.core.net.ip_addr.IpAddr.V6) := by
  cases r with
  | V4 a =>
      rcases RangeMore.range_max_spec a with ⟨o, ho, hvalue⟩
      refine ⟨o.map ipnet.core.net.ip_addr.IpAddr.V4, ?_, ?_, ?_, ?_⟩
      · simp [ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.max,
          ho, map_v4]
      · simpa [remaining, addrValue, Option.map_map, Function.comp_def] using hvalue
      · intro x hx
        cases o with
        | none => simp at hx
        | some y =>
            simp only [Option.map_some] at hx
            cases hx
            rfl
      · exact ⟨o, ho, rfl⟩
  | V6 a =>
      rcases IPv6RangeBasic.max_spec a with ⟨o, ho, hvalue⟩
      refine ⟨o.map ipnet.core.net.ip_addr.IpAddr.V6, ?_, ?_, ?_, ?_⟩
      · simp [ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.max,
          ho, map_v6]
      · rw [v6_last_value] at hvalue
        simpa [remaining, addrValue, Option.map_map, Function.comp_def] using hvalue
      · intro x hx
        cases o with
        | none => simp at hx
        | some y =>
            simp only [Option.map_some] at hx
            cases hx
            rfl
      · exact ⟨o, ho, rfl⟩
/-- The selected tagged `min` forwards the exact concrete address and keeps
    its family while observing the endpoint of the independent interval. -/
theorem min_spec (r : ipnet.ipext.IpAddrRange) :
    ∃ out,
      ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.min r =
        Result.ok out ∧
      out.map addrValue = RangeMore.firstValue (remaining r) ∧
      (∀ a, out = some a → addrFamily a = family r) ∧
      (match r with
       | .V4 a => ∃ o,
           ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.min a =
             Result.ok o ∧ out = o.map ipnet.core.net.ip_addr.IpAddr.V4
       | .V6 a => ∃ o,
           ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.min a =
             Result.ok o ∧ out = o.map ipnet.core.net.ip_addr.IpAddr.V6) := by
  cases r with
  | V4 a =>
      rcases RangeMore.range_min_spec a with ⟨o, ho, hvalue⟩
      refine ⟨o.map ipnet.core.net.ip_addr.IpAddr.V4, ?_, ?_, ?_, ?_⟩
      · simp [ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.min,
          ho, map_v4]
      · simpa [remaining, addrValue, Option.map_map, Function.comp_def] using hvalue
      · intro x hx
        cases o with
        | none => simp at hx
        | some y =>
            simp only [Option.map_some] at hx
            cases hx
            rfl
      · exact ⟨o, ho, rfl⟩
  | V6 a =>
      rcases IPv6RangeBasic.min_spec a with ⟨o, ho, hvalue⟩
      refine ⟨o.map ipnet.core.net.ip_addr.IpAddr.V6, ?_, ?_, ?_, ?_⟩
      · simp [ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.min,
          ho, map_v6]
      · rw [v6_first_value] at hvalue
        simpa [remaining, addrValue, Option.map_map, Function.comp_def] using hvalue
      · intro x hx
        cases o with
        | none => simp at hx
        | some y =>
            simp only [Option.map_some] at hx
            cases hx
            rfl
      · exact ⟨o, ho, rfl⟩
/-- Both tagged branches forward the exact concrete step and its raw updated
    state, while their numeric observation is the independent interval back step. -/
theorem next_back_spec (r : ipnet.ipext.IpAddrRange) :
    ∃ out r',
      ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpAddr.next_back r =
        Result.ok (out, r') ∧
      (out.map addrValue, remaining r') = RangeMore.backStep (remaining r) ∧
      family r' = family r ∧
      (∀ a, out = some a → addrFamily a = family r) ∧
      (match r with
       | .V4 a => ∃ o a',
           ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv4Addr.next_back a =
             Result.ok (o, a') ∧
           out = o.map ipnet.core.net.ip_addr.IpAddr.V4 ∧ r' = .V4 a'
       | .V6 a => ∃ o a',
           ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv6Addr.next_back a =
             Result.ok (o, a') ∧
           out = o.map ipnet.core.net.ip_addr.IpAddr.V6 ∧ r' = .V6 a') := by
  cases r with
  | V4 a =>
      rcases RangeMore.range_next_back_spec a with ⟨o, a', hnext, hmath⟩
      refine ⟨o.map ipnet.core.net.ip_addr.IpAddr.V4, .V4 a', ?_, ?_, rfl, ?_, ?_⟩
      · simp [ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpAddr.next_back,
          hnext, map_v4]
      · simpa [remaining, addrValue, Option.map_map, Function.comp_def] using hmath
      · intro x hx
        cases o with
        | none => simp at hx
        | some y =>
            simp only [Option.map_some] at hx
            cases hx
            rfl
      · exact ⟨o, a', hnext, rfl, rfl⟩
  | V6 a =>
      rcases IPv6RangeSteps.range_next_back_spec a with ⟨o, a', hnext, hmath⟩
      refine ⟨o.map ipnet.core.net.ip_addr.IpAddr.V6, .V6 a', ?_, ?_, rfl, ?_, ?_⟩
      · simp [ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpAddr.next_back,
          hnext, map_v6]
      · simpa [remaining, addrValue, Option.map_map, Function.comp_def] using hmath
      · intro x hx
        cases o with
        | none => simp at hx
        | some y =>
            simp only [Option.map_some] at hx
            cases hx
            rfl
      · exact ⟨o, a', hnext, rfl, rfl⟩

/-- Both tagged branches forward the exact concrete step and its raw updated
    state, while their numeric observation is the independent interval front skip. -/
theorem nth_spec (r : ipnet.ipext.IpAddrRange) (n : Usize)
    (h64 : System.Platform.numBits = 64) :
    ∃ out r',
      ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.nth r n =
        Result.ok (out, r') ∧
      (out.map addrValue, remaining r') = RangeMore.skipFront (remaining r) n.val ∧
      family r' = family r ∧
      (∀ a, out = some a → addrFamily a = family r) ∧
      (match r with
       | .V4 a => ∃ o a',
           ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.nth a n =
             Result.ok (o, a') ∧
           out = o.map ipnet.core.net.ip_addr.IpAddr.V4 ∧ r' = .V4 a'
       | .V6 a => ∃ o a',
           ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.nth a n =
             Result.ok (o, a') ∧
           out = o.map ipnet.core.net.ip_addr.IpAddr.V6 ∧ r' = .V6 a') := by
  cases r with
  | V4 a =>
      rcases RangeMore.range_nth_spec a n h64 with ⟨o, a', hnext, hmath⟩
      refine ⟨o.map ipnet.core.net.ip_addr.IpAddr.V4, .V4 a', ?_, ?_, rfl, ?_, ?_⟩
      · simp [ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.nth,
          hnext, map_v4]
      · simpa [remaining, addrValue, Option.map_map, Function.comp_def] using hmath
      · intro x hx
        cases o with
        | none => simp at hx
        | some y =>
            simp only [Option.map_some] at hx
            cases hx
            rfl
      · exact ⟨o, a', hnext, rfl, rfl⟩
  | V6 a =>
      rcases IPv6RangeSkips.nth_remaining_spec a n h64 with ⟨o, a', hnext, hmath⟩
      refine ⟨o.map ipnet.core.net.ip_addr.IpAddr.V6, .V6 a', ?_, ?_, rfl, ?_, ?_⟩
      · simp [ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.nth,
          hnext, map_v6]
      · simpa [remaining, addrValue, Option.map_map, Function.comp_def] using hmath
      · intro x hx
        cases o with
        | none => simp at hx
        | some y =>
            simp only [Option.map_some] at hx
            cases hx
            rfl
      · exact ⟨o, a', hnext, rfl, rfl⟩

/-- Both tagged branches forward the exact concrete step and its raw updated
    state, while their numeric observation is the independent interval back skip. -/
theorem nth_back_spec (r : ipnet.ipext.IpAddrRange) (n : Usize)
    (h64 : System.Platform.numBits = 64) :
    ∃ out r',
      ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpAddr.nth_back r n =
        Result.ok (out, r') ∧
      (out.map addrValue, remaining r') = RangeMore.skipBack (remaining r) n.val ∧
      family r' = family r ∧
      (∀ a, out = some a → addrFamily a = family r) ∧
      (match r with
       | .V4 a => ∃ o a',
           ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv4Addr.nth_back a n =
             Result.ok (o, a') ∧
           out = o.map ipnet.core.net.ip_addr.IpAddr.V4 ∧ r' = .V4 a'
       | .V6 a => ∃ o a',
           ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpv6Addr.nth_back a n =
             Result.ok (o, a') ∧
           out = o.map ipnet.core.net.ip_addr.IpAddr.V6 ∧ r' = .V6 a') := by
  cases r with
  | V4 a =>
      rcases RangeMore.range_nth_back_spec a n h64 with ⟨o, a', hnext, hmath⟩
      refine ⟨o.map ipnet.core.net.ip_addr.IpAddr.V4, .V4 a', ?_, ?_, rfl, ?_, ?_⟩
      · simp [ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpAddr.nth_back,
          hnext, map_v4]
      · simpa [remaining, addrValue, Option.map_map, Function.comp_def] using hmath
      · intro x hx
        cases o with
        | none => simp at hx
        | some y =>
            simp only [Option.map_some] at hx
            cases hx
            rfl
      · exact ⟨o, a', hnext, rfl, rfl⟩

  | V6 a =>
      rcases IPv6RangeSkips.nth_back_remaining_spec a n h64 with ⟨o, a', hnext, hmath⟩
      refine ⟨o.map ipnet.core.net.ip_addr.IpAddr.V6, .V6 a', ?_, ?_, rfl, ?_, ?_⟩
      · simp [ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorIpAddr.nth_back,
          hnext, map_v6]
      · simpa [remaining, addrValue, Option.map_map, Function.comp_def] using hmath
      · intro x hx
        cases o with
        | none => simp at hx
        | some y =>
            simp only [Option.map_some] at hx
            cases hx
            rfl
      · exact ⟨o, a', hnext, rfl, rfl⟩


private theorem v6_size_eq_card (r : ipnet.ipext.Ipv6AddrRange) :
    RangeMath.size (IPv6RangeSteps.remaining r) =
      IPv6RangeMath.card (CidrModel.ipv6Value r.start)
        (CidrModel.ipv6Value r.end) := by
  simp [IPv6RangeSteps.remaining, IPv6RangeMath.remaining,
    RangeMath.size_ofInclusive, IPv6RangeMath.card]

private theorem v4_size_le_usizeMax (r : ipnet.ipext.Ipv4AddrRange) :
    RangeMath.size (RangeNext.remaining r) ≤ IPv6RangeMath.usizeMax := by
  have he : CidrModel.ipv4Value r.end < 2^32 :=
    CidrModel.ipv4Value_bound r.end
  simp [RangeNext.remaining, RangeMath.size_ofInclusive,
    IPv6RangeMath.usizeMax, IPv6RangeMath.usizeLimit]
  split_ifs <;> omega

@[expose] def expectedHint (r : ipnet.ipext.IpAddrRange) : Nat × Option Nat :=
  let n := RangeMath.size (remaining r)
  if n ≤ IPv6RangeMath.usizeMax then (n, some n)
  else (IPv6RangeMath.usizeMax, none)

/-- Both full-family branches return the independent pinned-64 cardinality
    hint, including the full IPv6 space, by exact concrete forwarding. -/
theorem size_hint_spec (r : ipnet.ipext.IpAddrRange)
    (h64 : System.Platform.numBits = 64) :
    ∃ lower upper,
      ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.size_hint r =
        Result.ok (lower, upper) ∧
      (lower.val, upper.map UScalar.val) = expectedHint r ∧
      (match r with
       | .V4 a =>
           ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.size_hint a =
             Result.ok (lower, upper)
       | .V6 a =>
           ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.size_hint a =
             Result.ok (lower, upper)) := by
  cases r with
  | V4 a =>
      rcases RangeMore.range_size_hint_spec a h64 with ⟨lo, up, hhint, hval, hup⟩
      refine ⟨lo, up, ?_, ?_, hhint⟩
      · simpa [ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.size_hint]
          using hhint
      · have hfit := v4_size_le_usizeMax a
        simp [expectedHint, remaining, hfit, hup, hval]
  | V6 a =>
      rcases IPv6RangeSkips.size_hint_spec a h64 with ⟨lo, up, hhint, hmodel⟩
      refine ⟨lo, up, ?_, ?_, hhint⟩
      · simpa [ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.size_hint]
          using hhint
      · simpa [expectedHint, remaining, v6_size_eq_card,
          IPv6RangeMath.sizeHint] using hmodel

/-- The tagged count preserves concrete delegation and its exact pinned-64
    success/overflow split for both families and every raw endpoint pair. -/
theorem count_spec (r : ipnet.ipext.IpAddrRange)
    (h64 : System.Platform.numBits = 64) :
    ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.count r =
      (match r with
       | .V4 a =>
           ipnet.ipext.Ipv4AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv4Addr.count a
       | .V6 a =>
           ipnet.ipext.Ipv6AddrRange.Insts.CoreIterTraitsIteratorIteratorIpv6Addr.count a) ∧
    (RangeMath.size (remaining r) ≤ IPv6RangeMath.usizeMax →
      ∃ out,
        ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.count r =
          Result.ok out ∧ out.val = RangeMath.size (remaining r)) ∧
    (IPv6RangeMath.usizeMax < RangeMath.size (remaining r) →
      ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.count r =
        Result.fail .integerOverflow) := by
  constructor
  · cases r <;>
      rfl
  constructor
  · intro hfit
    cases r with
    | V4 a =>
        rcases RangeMore.range_count_spec a h64 with ⟨out, hout, hval⟩
        refine ⟨out, ?_, ?_⟩
        · simpa [ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.count]
            using hout
        · simpa [remaining] using hval
    | V6 a =>
        have hcard : IPv6RangeMath.card (CidrModel.ipv6Value a.start)
            (CidrModel.ipv6Value a.end) ≤ IPv6RangeMath.usizeMax := by
          simpa [remaining, v6_size_eq_card] using hfit
        rcases IPv6RangeBasic.count_normal_spec a h64 hcard with
          ⟨out, hout, hval⟩
        refine ⟨out, ?_, ?_⟩
        · simpa [ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.count]
            using hout
        · simpa [remaining, v6_size_eq_card] using hval
  · intro hbig
    cases r with
    | V4 a =>
        have hbound := v4_size_le_usizeMax a
        simp only [remaining] at hbig
        omega
    | V6 a =>
        have hcard : IPv6RangeMath.usizeMax <
            IPv6RangeMath.card (CidrModel.ipv6Value a.start)
              (CidrModel.ipv6Value a.end) := by
          simpa [remaining, v6_size_eq_card] using hbig
        have hfail := IPv6RangeBasic.count_overflow_spec a h64 hcard
        simpa [ipnet.ipext.IpAddrRange.Insts.CoreIterTraitsIteratorIteratorIpAddr.count]
          using hfail

end TaggedRange
