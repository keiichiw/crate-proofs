module
public import Proofs.Arithmetic
public import Proofs.Collections
public import Proofs.RangeMath
public import Proofs.Contains
public import Proofs.IPv6NetMath

public section

namespace IPv6NetOps

open Aeneas Aeneas.Std Result

@[expose] def remaining (r : ipnet.ipext.Ipv6AddrRange) : RangeMath.HalfOpen :=
  RangeMath.ofInclusive (CidrModel.ipv6Value r.start)
    (CidrModel.ipv6Value r.end)

/-- Every valid IPv6 network returns all addresses in its CIDR block,
including both endpoints for /127 and /128. -/
theorem hosts_spec (n : ipnet.ipnet.Ipv6Net)
    (hp : n.prefix_len.val ≤ 128) :
    ∃ out, ipnet.ipnet.Ipv6Net.hosts n = Result.ok out ∧
      CidrModel.ipv6Value out.start =
        CidrModel.lower 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val ∧
      CidrModel.ipv6Value out.end =
        CidrModel.upper 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val ∧
      remaining out = RangeMath.ofInclusive
        (CidrModel.lower 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val)
        (CidrModel.upper 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val) := by
  rcases ipnet.ipv6_network_nat_spec n hp with ⟨start, hstart, hvstart⟩
  rcases ipnet.ipv6_broadcast_nat_spec n hp with ⟨stop, hstop, hvstop⟩
  let out : ipnet.ipext.Ipv6AddrRange := { start, «end» := stop }
  refine ⟨out, ?_, ?_, ?_, ?_⟩
  · simp [ipnet.ipnet.Ipv6Net.hosts, hstart, hstop,
      ipnet.ipext.Ipv6AddrRange.new, out]
  · exact hvstart
  · exact hvstop
  · simp [remaining, out, hvstart, hvstop]

/-- The selected constructor validates every U8 prefix and initializes raw
endpoints; enumeration is a separate contract. -/
theorem subnets_spec (n : ipnet.ipnet.Ipv6Net) (q : U8)
    (hp : n.prefix_len.val ≤ 128) :
    ∃ out : core.result.Result ipnet.ipnet.Ipv6Subnets ipnet.ipnet.PrefixLenError,
      ipnet.ipnet.Ipv6Net.subnets n q = Result.ok out ∧
      (if q.val < n.prefix_len.val ∨ 128 < q.val then
         out = .Err ()
       else
         ∃ s, out = .Ok s ∧
           CidrModel.ipv6Value s.start =
             CidrModel.lower 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val ∧
           CidrModel.ipv6Value s.end =
             CidrModel.upper 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val ∧
           s.min_prefix_len = q) := by
  by_cases hlow : q.val < n.prefix_len.val
  · refine ⟨.Err (), ?_, ?_⟩
    · simp [ipnet.ipnet.Ipv6Net.subnets, hlow]
    · simp [hlow]
  · by_cases hhigh : 128 < q.val
    · refine ⟨.Err (), ?_, ?_⟩
      · simp [ipnet.ipnet.Ipv6Net.subnets, hlow, hhigh]
      · simp [hhigh]
    · rcases ipnet.ipv6_network_nat_spec n hp with ⟨start, hstart, hvstart⟩
      rcases ipnet.ipv6_broadcast_nat_spec n hp with ⟨stop, hstop, hvstop⟩
      let sub : ipnet.ipnet.Ipv6Subnets :=
        { start, «end» := stop, min_prefix_len := q }
      refine ⟨.Ok sub, ?_, ?_⟩
      · simp [ipnet.ipnet.Ipv6Net.subnets, hlow, hhigh, hstart, hstop,
          ipnet.ipnet.Ipv6Subnets.new, sub]
      · simp [hlow, hhigh, sub, hvstart, hvstop]

private theorem wrapping_pred_zero (p : U8) (h : p.val = 0) :
    (core.num.U8.wrapping_sub p 1#u8).val = 255 := by
  rw [core.num.U8.wrapping_sub_val_eq]
  norm_num [U8.size_eq] at *
  omega

private theorem wrapping_pred_positive (p : U8) (h : 0 < p.val) :
    (core.num.U8.wrapping_sub p 1#u8).val = p.val - 1 := by
  rw [core.num.U8.wrapping_sub_val_eq]
  have hp := U8.lt_succ_max p
  norm_num [U8.size_eq] at *
  omega

/-- The extracted `supernet` body returns no parent only for /0, and otherwise
    returns the canonical immediate parent of every valid raw network. -/
theorem supernet_spec (n : ipnet.ipnet.Ipv6Net)
    (hp : n.prefix_len.val ≤ 128) :
    ∃ out, ipnet.ipnet.Ipv6Net.supernet n = Result.ok out ∧
      (if n.prefix_len.val = 0 then out = none else
        ∃ parent, out = some parent ∧
          parent.prefix_len.val = n.prefix_len.val - 1 ∧
          CidrModel.ipv6Value parent.addr =
            CidrModel.lower 128 (CidrModel.ipv6Value n.addr)
              (n.prefix_len.val - 1) ∧
          parent.prefix_len.val ≤ 128 ∧
          CidrModel.subset 128 (CidrModel.ipv6Value parent.addr)
            parent.prefix_len.val (CidrModel.ipv6Value n.addr) n.prefix_len.val) := by
  let p : U8 := core.num.U8.wrapping_sub n.prefix_len 1#u8
  by_cases hzero : n.prefix_len.val = 0
  · have hpbad : 128 < p.val := by
      dsimp [p]
      rw [wrapping_pred_zero n.prefix_len hzero]
      omega
    have hpbad' : 128 <
        (n.prefix_len.val + (U8.size - 1)) % U8.size := by
      simpa [p, core.num.U8.wrapping_sub_val_eq] using hpbad
    refine ⟨none, ?_, by simp [hzero]⟩
    simp [ipnet.ipnet.Ipv6Net.supernet, ipnet.ipnet.Ipv6Net.new,
      hpbad', ipnet.core.result.Result.map, core.result.Result.to_option,
      lift, bind_ok]
  · have hpos : 0 < n.prefix_len.val := by omega
    have hpval : p.val = n.prefix_len.val - 1 := by
      exact wrapping_pred_positive n.prefix_len hpos
    have hpvalid : p.val ≤ 128 := by omega
    have hpvalid' : ¬ 128 <
        (n.prefix_len.val + (U8.size - 1)) % U8.size := by
      simpa [p, core.num.U8.wrapping_sub_val_eq] using hpvalid
    rcases ipnet.ipv6_trunc_nat_spec
      { addr := n.addr, prefix_len := p } hpvalid with
      ⟨parent, htrunc, hparentp, hparentv⟩
    refine ⟨some parent, ?_, ?_⟩
    · simp [ipnet.ipnet.Ipv6Net.supernet, ipnet.ipnet.Ipv6Net.new,
        hpvalid', ipnet.core.result.Result.map,
        ipnet.ipnet.Ipv6Net.supernet.closure.Insts.CoreOpsFunctionFnOnceTupleIpv6NetIpv6Net.call_once,
        core.result.Result.to_option, lift, bind_ok]
      change (do
        let value ← ipnet.ipnet.Ipv6Net.trunc { addr := n.addr, prefix_len := p }
        Result.ok (some value)) = Result.ok (some parent)
      simp [htrunc]
    · simp only [hzero, ↓reduceIte]
      refine ⟨parent, rfl, ?_, ?_, ?_, ?_⟩
      · have hv := congrArg UScalar.val hparentp
        simpa [hpval] using hv
      · simpa [hpval] using hparentv
      · have hv := congrArg UScalar.val hparentp
        rw [hv]
        exact hpvalid
      · have hparentlower :
            CidrModel.lower 128 (CidrModel.ipv6Value parent.addr)
              (n.prefix_len.val - 1) =
            CidrModel.lower 128 (CidrModel.ipv6Value n.addr)
              (n.prefix_len.val - 1) := by
          have hv' : CidrModel.ipv6Value parent.addr =
              CidrModel.lower 128 (CidrModel.ipv6Value n.addr)
                (n.prefix_len.val - 1) := by
            simpa [hpval] using hparentv
          rw [hv', CidrModel.lower_normalize]
        have hbase := IPv6NetMath.parent_contains_child
          (CidrModel.ipv6Value n.addr) n.prefix_len.val hpos hp
        have hv := congrArg UScalar.val hparentp
        rw [hv, hpval]
        intro x hx
        exact (CidrModel.member_eq_of_lower_eq 128
          (CidrModel.ipv6Value parent.addr) (CidrModel.ipv6Value n.addr)
          (n.prefix_len.val - 1) x hparentlower).mpr (hbase x hx)

/-- The actual sibling check is equivalent to equality of immediate parent
    blocks, for all valid raw networks, including self-comparison. -/
theorem is_sibling_spec (n m : ipnet.ipnet.Ipv6Net)
    (hn : n.prefix_len.val ≤ 128) (hm : m.prefix_len.val ≤ 128) :
    ∃ out, ipnet.ipnet.Ipv6Net.is_sibling n m = Result.ok out ∧
      (out = true ↔
        0 < n.prefix_len.val ∧ n.prefix_len.val = m.prefix_len.val ∧
        CidrModel.lower 128 (CidrModel.ipv6Value n.addr)
          (n.prefix_len.val - 1) =
        CidrModel.lower 128 (CidrModel.ipv6Value m.addr)
          (m.prefix_len.val - 1)) := by
  by_cases hpos : 0 < n.prefix_len.val
  · by_cases heq : n.prefix_len = m.prefix_len
    · have hmval : m.prefix_len.val = n.prefix_len.val :=
        congrArg UScalar.val heq.symm
      have hmpos : 0 < m.prefix_len.val := by omega
      rcases supernet_spec n hn with ⟨o, hsuper, hpost⟩
      have hnzero : ¬ n.prefix_len.val = 0 := by omega
      simp only [hnzero, ↓reduceIte] at hpost
      rcases hpost with ⟨parent, ho, hparentp, hparentv, hparentvalid, _⟩
      rcases ipnet.ipv6_contains_net_spec parent m hparentvalid hm with
        ⟨b, hcontains, hb⟩
      have hsubset :
          CidrModel.subset 128 (CidrModel.ipv6Value parent.addr)
            parent.prefix_len.val (CidrModel.ipv6Value m.addr) m.prefix_len.val ↔
          CidrModel.lower 128 (CidrModel.ipv6Value parent.addr)
            (n.prefix_len.val - 1) =
          CidrModel.lower 128 (CidrModel.ipv6Value m.addr)
            (m.prefix_len.val - 1) := by
        simpa [hparentp, hmval] using
          IPv6NetMath.parent_contains_child_iff_same_parent
            (CidrModel.ipv6Value parent.addr) (CidrModel.ipv6Value m.addr)
            n.prefix_len.val hpos hn
      have hparentlower :
          CidrModel.lower 128 (CidrModel.ipv6Value parent.addr)
            (n.prefix_len.val - 1) =
          CidrModel.lower 128 (CidrModel.ipv6Value n.addr)
            (n.prefix_len.val - 1) := by
        rw [hparentv, CidrModel.lower_normalize]
      refine ⟨b, ?_, ?_⟩
      · simp [ipnet.ipnet.Ipv6Net.is_sibling, hmpos, heq, hsuper, ho,
          core.option.Option.unwrap, ipnet.ipnet.Ipv6Net.contains,
          hcontains, bind_ok]
      · rw [hb, hsubset, hparentlower]
        simp [hpos, heq, hmval]
    · refine ⟨false, ?_, ?_⟩
      · simp [ipnet.ipnet.Ipv6Net.is_sibling, hpos, heq]
      · have hneq : n.prefix_len.val ≠ m.prefix_len.val := by
          intro hv
          apply heq
          exact UScalar.eq_of_val_eq hv
        simp [hneq]
  · refine ⟨false, ?_, ?_⟩
    · simp [ipnet.ipnet.Ipv6Net.is_sibling, hpos]
    · simp [hpos]

end IPv6NetOps
