module
public import Proofs.Arithmetic
public import Proofs.Collections
public import Proofs.RangeNext
public import Proofs.IPv4NetMath

public section

namespace IPv4NetOps

open Aeneas Aeneas.Std Result

/-- The selected Rust `Default` implementation gives the full IPv4 /0. -/
theorem default_spec :
    ∃ out, ipnet.ipnet.Ipv4Net.Insts.CoreDefaultDefault.default = Result.ok out ∧
      CidrModel.ipv4Value out.addr = 0 ∧ out.prefix_len = 0#u8 := by
  rcases AddressConversions.ipv4_from_u32_spec 0#u32 with ⟨addr, haddr, hval⟩
  refine ⟨{ addr, prefix_len := 0#u8 }, ?_, hval, rfl⟩
  simp [ipnet.ipnet.Ipv4Net.Insts.CoreDefaultDefault.default, haddr]

/-- `From<Ipv4Addr>` preserves the exact address and forms a /32 singleton. -/
theorem from_ipv4_spec (addr : ipnet.core.net.ip_addr.Ipv4Addr) :
    ipnet.ipnet.Ipv4Net.Insts.CoreConvertFromIpv4Addr.from addr =
      Result.ok { addr := addr, prefix_len := 32#u8 } := by
  rfl

/-- The existing U32 subtraction model and extracted address conversion give
    the exact numeric result for every address and scalar operand. -/
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

/-- For every valid raw network, `hosts` returns exact raw endpoints and the
    independent half-open host interval, including /0, /31, and /32. -/
theorem hosts_spec (n : ipnet.ipnet.Ipv4Net)
    (hp : n.prefix_len.val ≤ 32) :
    ∃ out, ipnet.ipnet.Ipv4Net.hosts n = Result.ok out ∧
      CidrModel.ipv4Value out.start =
        IPv4NetMath.hostStart (CidrModel.ipv4Value n.addr) n.prefix_len.val ∧
      CidrModel.ipv4Value out.end =
        IPv4NetMath.hostStop (CidrModel.ipv4Value n.addr) n.prefix_len.val ∧
      RangeNext.remaining out =
        IPv4NetMath.hostsRemaining (CidrModel.ipv4Value n.addr) n.prefix_len.val := by
  rcases ipnet.ipv4_network_nat_spec n hp with ⟨start, hstart, hvstart⟩
  rcases ipnet.ipv4_broadcast_nat_spec n hp with ⟨stop, hstop, hvstop⟩
  by_cases hlt : n.prefix_len.val < 31
  · rcases RangeNext.ipv4_saturating_add_spec start 1#u32 with
      ⟨start1, hadd, hvadd⟩
    rcases ipv4_saturating_sub_spec stop 1#u32 with
      ⟨stop1, hsub, hvsub⟩
    have hstartv : CidrModel.ipv4Value start1 =
        IPv4NetMath.hostStart (CidrModel.ipv4Value n.addr) n.prefix_len.val := by
      rw [hvadd, hvstart]
      simpa [IPv4NetMath.hostStart, hlt, RangeMath.maxAddress,
        RangeMath.limit] using
        IPv4NetMath.host_start_no_saturation
          (CidrModel.ipv4Value n.addr) n.prefix_len.val hlt
          (by simpa [RangeMath.limit] using CidrModel.ipv4Value_bound n.addr)
    have hstopv : CidrModel.ipv4Value stop1 =
        IPv4NetMath.hostStop (CidrModel.ipv4Value n.addr) n.prefix_len.val := by
      rw [hvsub, hvstop]
      simp [IPv4NetMath.hostStop, hlt]
    let out : ipnet.ipext.Ipv4AddrRange := { start := start1, «end» := stop1 }
    refine ⟨out, ?_, ?_, ?_, ?_⟩
    · simp [ipnet.ipnet.Ipv4Net.hosts, hstart, hstop, hlt, hadd, hsub,
        ipnet.ipext.Ipv4AddrRange.new, out]
    · exact hstartv
    · exact hstopv
    · change RangeMath.ofInclusive (CidrModel.ipv4Value start1)
          (CidrModel.ipv4Value stop1) =
          RangeMath.ofInclusive
            (IPv4NetMath.hostStart (CidrModel.ipv4Value n.addr) n.prefix_len.val)
            (IPv4NetMath.hostStop (CidrModel.ipv4Value n.addr) n.prefix_len.val)
      rw [hstartv, hstopv]
  · let out : ipnet.ipext.Ipv4AddrRange := { start, «end» := stop }
    refine ⟨out, ?_, ?_, ?_, ?_⟩
    · simp [ipnet.ipnet.Ipv4Net.hosts, hstart, hstop, hlt,
        ipnet.ipext.Ipv4AddrRange.new, out]
    · simpa [out, IPv4NetMath.hostStart, hlt] using hvstart
    · simpa [out, IPv4NetMath.hostStop, hlt] using hvstop
    · simp [RangeNext.remaining, IPv4NetMath.hostsRemaining, out,
        IPv4NetMath.hostStart, IPv4NetMath.hostStop, hlt, hvstart, hvstop]

/-- The selected `subnets` body validates every U8 prefix and initializes the
    iterator with exact network/broadcast endpoints. Iteration is separate. -/
theorem subnets_spec (n : ipnet.ipnet.Ipv4Net) (q : U8)
    (hp : n.prefix_len.val ≤ 32) :
    ∃ out : core.result.Result ipnet.ipnet.Ipv4Subnets ipnet.ipnet.PrefixLenError,
      ipnet.ipnet.Ipv4Net.subnets n q = Result.ok out ∧
      (if q.val < n.prefix_len.val ∨ 32 < q.val then
         out = .Err ()
       else
         ∃ s, out = .Ok s ∧
           CidrModel.ipv4Value s.start =
             CidrModel.lower 32 (CidrModel.ipv4Value n.addr) n.prefix_len.val ∧
           CidrModel.ipv4Value s.end =
             CidrModel.upper 32 (CidrModel.ipv4Value n.addr) n.prefix_len.val ∧
           s.min_prefix_len = q) := by
  by_cases hlow : q.val < n.prefix_len.val
  · refine ⟨.Err (), ?_, ?_⟩
    · simp [ipnet.ipnet.Ipv4Net.subnets, hlow]
    · simp [hlow]
  · by_cases hhigh : 32 < q.val
    · refine ⟨.Err (), ?_, ?_⟩
      · simp [ipnet.ipnet.Ipv4Net.subnets, hlow, hhigh]
      · simp [hhigh]
    · rcases ipnet.ipv4_network_nat_spec n hp with ⟨start, hstart, hvstart⟩
      rcases ipnet.ipv4_broadcast_nat_spec n hp with ⟨stop, hstop, hvstop⟩
      let sub : ipnet.ipnet.Ipv4Subnets :=
        { start, «end» := stop, min_prefix_len := q }
      refine ⟨.Ok sub, ?_, ?_⟩
      · simp [ipnet.ipnet.Ipv4Net.subnets, hlow, hhigh, hstart, hstop,
          ipnet.ipnet.Ipv4Subnets.new, sub]
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
theorem supernet_spec (n : ipnet.ipnet.Ipv4Net)
    (hp : n.prefix_len.val ≤ 32) :
    ∃ out, ipnet.ipnet.Ipv4Net.supernet n = Result.ok out ∧
      (if n.prefix_len.val = 0 then out = none else
        ∃ parent, out = some parent ∧
          parent.prefix_len.val = n.prefix_len.val - 1 ∧
          CidrModel.ipv4Value parent.addr =
            CidrModel.lower 32 (CidrModel.ipv4Value n.addr)
              (n.prefix_len.val - 1) ∧
          parent.prefix_len.val ≤ 32 ∧
          CidrModel.subset 32 (CidrModel.ipv4Value parent.addr)
            parent.prefix_len.val (CidrModel.ipv4Value n.addr) n.prefix_len.val) := by
  let p : U8 := core.num.U8.wrapping_sub n.prefix_len 1#u8
  by_cases hzero : n.prefix_len.val = 0
  · have hpbad : 32 < p.val := by
      dsimp [p]
      rw [wrapping_pred_zero n.prefix_len hzero]
      omega
    have hpbad' : 32 <
        (n.prefix_len.val + (U8.size - 1)) % U8.size := by
      simpa [p, core.num.U8.wrapping_sub_val_eq] using hpbad
    refine ⟨none, ?_, by simp [hzero]⟩
    simp [ipnet.ipnet.Ipv4Net.supernet, ipnet.ipnet.Ipv4Net.new,
      hpbad', ipnet.core.result.Result.map, core.result.Result.to_option,
      lift, bind_ok]
  · have hpos : 0 < n.prefix_len.val := by omega
    have hpval : p.val = n.prefix_len.val - 1 := by
      exact wrapping_pred_positive n.prefix_len hpos
    have hpvalid : p.val ≤ 32 := by omega
    have hpvalid' : ¬ 32 <
        (n.prefix_len.val + (U8.size - 1)) % U8.size := by
      simpa [p, core.num.U8.wrapping_sub_val_eq] using hpvalid
    rcases ipnet.ipv4_trunc_nat_spec
      { addr := n.addr, prefix_len := p } hpvalid with
      ⟨parent, htrunc, hparentp, hparentv⟩
    refine ⟨some parent, ?_, ?_⟩
    · simp [ipnet.ipnet.Ipv4Net.supernet, ipnet.ipnet.Ipv4Net.new,
        hpvalid', ipnet.core.result.Result.map,
        ipnet.ipnet.Ipv4Net.supernet.closure.Insts.CoreOpsFunctionFnOnceTupleIpv4NetIpv4Net.call_once,
        core.result.Result.to_option, lift, bind_ok]
      change (do
        let value ← ipnet.ipnet.Ipv4Net.trunc { addr := n.addr, prefix_len := p }
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
            CidrModel.lower 32 (CidrModel.ipv4Value parent.addr)
              (n.prefix_len.val - 1) =
            CidrModel.lower 32 (CidrModel.ipv4Value n.addr)
              (n.prefix_len.val - 1) := by
          have hv' : CidrModel.ipv4Value parent.addr =
              CidrModel.lower 32 (CidrModel.ipv4Value n.addr)
                (n.prefix_len.val - 1) := by
            simpa [hpval] using hparentv
          rw [hv', CidrModel.lower_normalize]
        have hbase := IPv4NetMath.parent_contains_child
          (CidrModel.ipv4Value n.addr) n.prefix_len.val hpos hp
        have hv := congrArg UScalar.val hparentp
        rw [hv, hpval]
        intro x hx
        exact (CidrModel.member_eq_of_lower_eq 32
          (CidrModel.ipv4Value parent.addr) (CidrModel.ipv4Value n.addr)
          (n.prefix_len.val - 1) x hparentlower).mpr (hbase x hx)

/-- The actual sibling check is equivalent to equality of immediate parent
    blocks, for all valid raw networks, including self-comparison. -/
theorem is_sibling_spec (n m : ipnet.ipnet.Ipv4Net)
    (hn : n.prefix_len.val ≤ 32) (hm : m.prefix_len.val ≤ 32) :
    ∃ out, ipnet.ipnet.Ipv4Net.is_sibling n m = Result.ok out ∧
      (out = true ↔
        0 < n.prefix_len.val ∧ n.prefix_len.val = m.prefix_len.val ∧
        CidrModel.lower 32 (CidrModel.ipv4Value n.addr)
          (n.prefix_len.val - 1) =
        CidrModel.lower 32 (CidrModel.ipv4Value m.addr)
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
      rcases ipnet.ipv4_contains_net_spec parent m hparentvalid hm with
        ⟨b, hcontains, hb⟩
      have hsubset :
          CidrModel.subset 32 (CidrModel.ipv4Value parent.addr)
            parent.prefix_len.val (CidrModel.ipv4Value m.addr) m.prefix_len.val ↔
          CidrModel.lower 32 (CidrModel.ipv4Value parent.addr)
            (n.prefix_len.val - 1) =
          CidrModel.lower 32 (CidrModel.ipv4Value m.addr)
            (m.prefix_len.val - 1) := by
        simpa [hparentp, hmval] using
          IPv4NetMath.parent_contains_child_iff_same_parent
            (CidrModel.ipv4Value parent.addr) (CidrModel.ipv4Value m.addr)
            n.prefix_len.val hpos hn
      have hparentlower :
          CidrModel.lower 32 (CidrModel.ipv4Value parent.addr)
            (n.prefix_len.val - 1) =
          CidrModel.lower 32 (CidrModel.ipv4Value n.addr)
            (n.prefix_len.val - 1) := by
        rw [hparentv, CidrModel.lower_normalize]
      refine ⟨b, ?_, ?_⟩
      · simp [ipnet.ipnet.Ipv4Net.is_sibling, hmpos, heq, hsuper, ho,
          core.option.Option.unwrap, ipnet.ipnet.Ipv4Net.contains,
          hcontains, bind_ok]
      · rw [hb, hsubset, hparentlower]
        simp [hpos, heq, hmval]
    · refine ⟨false, ?_, ?_⟩
      · simp [ipnet.ipnet.Ipv4Net.is_sibling, hpos, heq]
      · have hneq : n.prefix_len.val ≠ m.prefix_len.val := by
          intro hv
          apply heq
          exact UScalar.eq_of_val_eq hv
        simp [hneq]
  · refine ⟨false, ?_, ?_⟩
    · simp [ipnet.ipnet.Ipv4Net.is_sibling, hpos]
    · simp [hpos]

end IPv4NetOps
