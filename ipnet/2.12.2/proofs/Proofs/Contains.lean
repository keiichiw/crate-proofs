module
public import Proofs.Arithmetic
public import Proofs.Comparisons
public section

open Aeneas Aeneas.Std Result

namespace ipnet

private theorem le4 (a b : core.net.ip_addr.Ipv4Addr) :
    core.cmp.PartialOrd.le.trait_default
      core.net.ip_addr.Ipv4Addr.Insts.CoreCmpPartialOrdIpv4Addr a b =
      Result.ok (decide (CidrModel.ipv4Value a ≤ CidrModel.ipv4Value b)) :=
  Comparisons.ipv4_le_spec a b

private theorem le6 (a b : core.net.ip_addr.Ipv6Addr) :
    core.cmp.PartialOrd.le.trait_default
      core.net.ip_addr.Ipv6Addr.Insts.CoreCmpPartialOrdIpv6Addr a b =
      Result.ok (decide (CidrModel.ipv6Value a ≤ CidrModel.ipv6Value b)) :=
  Comparisons.ipv6_le_spec a b

/-- The extracted IPv4 address containment body returns the independent CIDR membership test. -/
theorem ipv4_contains_addr_result (n : ipnet.Ipv4Net)
    (a : core.net.ip_addr.Ipv4Addr) (hp : n.prefix_len.val ≤ 32) :
    ipnet.Ipv4Net.Insts.IpnetIpnetContainsSharedAIpv4Addr.contains n a =
      Result.ok (decide (CidrModel.lower 32 (CidrModel.ipv4Value n.addr) n.prefix_len.val ≤ CidrModel.ipv4Value a ∧
        CidrModel.ipv4Value a ≤ CidrModel.upper 32 (CidrModel.ipv4Value n.addr) n.prefix_len.val)) := by
  rcases ipv4_network_nat_spec n hp with ⟨lo, hlo, hloV⟩
  rcases ipv4_broadcast_nat_spec n hp with ⟨hi, hhi, hhiV⟩
  simp only [ipnet.Ipv4Net.Insts.IpnetIpnetContainsSharedAIpv4Addr.contains,
    hlo, hhi, le4, hloV, hhiV, bind_ok]
  by_cases h : CidrModel.lower 32 (CidrModel.ipv4Value n.addr) n.prefix_len.val ≤ CidrModel.ipv4Value a <;> simp [h]

/-- The extracted IPv6 address containment body returns the independent CIDR membership test. -/
theorem ipv6_contains_addr_result (n : ipnet.Ipv6Net)
    (a : core.net.ip_addr.Ipv6Addr) (hp : n.prefix_len.val ≤ 128) :
    ipnet.Ipv6Net.Insts.IpnetIpnetContainsSharedAIpv6Addr.contains n a =
      Result.ok (decide (CidrModel.lower 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val ≤ CidrModel.ipv6Value a ∧
        CidrModel.ipv6Value a ≤ CidrModel.upper 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val)) := by
  rcases ipv6_network_nat_spec n hp with ⟨lo, hlo, hloV⟩
  rcases ipv6_broadcast_nat_spec n hp with ⟨hi, hhi, hhiV⟩
  simp only [ipnet.Ipv6Net.Insts.IpnetIpnetContainsSharedAIpv6Addr.contains,
    hlo, hhi, le6, hloV, hhiV, bind_ok]
  by_cases h : CidrModel.lower 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val ≤ CidrModel.ipv6Value a <;> simp [h]

/-- The extracted IPv4 network containment body compares both exact interval endpoints. -/
theorem ipv4_contains_net_result (n m : ipnet.Ipv4Net)
    (hn : n.prefix_len.val ≤ 32) (hm : m.prefix_len.val ≤ 32) :
    ipnet.Ipv4Net.Insts.IpnetIpnetContainsSharedAIpv4Net.contains n m =
      Result.ok (decide (CidrModel.lower 32 (CidrModel.ipv4Value n.addr) n.prefix_len.val ≤
        CidrModel.lower 32 (CidrModel.ipv4Value m.addr) m.prefix_len.val ∧
        CidrModel.upper 32 (CidrModel.ipv4Value m.addr) m.prefix_len.val ≤
        CidrModel.upper 32 (CidrModel.ipv4Value n.addr) n.prefix_len.val)) := by
  rcases ipv4_network_nat_spec n hn with ⟨loN, hloN, hloNV⟩
  rcases ipv4_network_nat_spec m hm with ⟨loM, hloM, hloMV⟩
  rcases ipv4_broadcast_nat_spec n hn with ⟨hiN, hhiN, hhiNV⟩
  rcases ipv4_broadcast_nat_spec m hm with ⟨hiM, hhiM, hhiMV⟩
  simp only [ipnet.Ipv4Net.Insts.IpnetIpnetContainsSharedAIpv4Net.contains,
    hloN, hloM, hhiN, hhiM, le4,
    hloNV, hloMV, hhiNV, hhiMV, bind_ok]
  by_cases h : CidrModel.lower 32 (CidrModel.ipv4Value n.addr) n.prefix_len.val ≤
      CidrModel.lower 32 (CidrModel.ipv4Value m.addr) m.prefix_len.val <;> simp [h]

/-- The extracted IPv6 network containment body compares both exact interval endpoints. -/
theorem ipv6_contains_net_result (n m : ipnet.Ipv6Net)
    (hn : n.prefix_len.val ≤ 128) (hm : m.prefix_len.val ≤ 128) :
    ipnet.Ipv6Net.Insts.IpnetIpnetContainsSharedAIpv6Net.contains n m =
      Result.ok (decide (CidrModel.lower 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val ≤
        CidrModel.lower 128 (CidrModel.ipv6Value m.addr) m.prefix_len.val ∧
        CidrModel.upper 128 (CidrModel.ipv6Value m.addr) m.prefix_len.val ≤
        CidrModel.upper 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val)) := by
  rcases ipv6_network_nat_spec n hn with ⟨loN, hloN, hloNV⟩
  rcases ipv6_network_nat_spec m hm with ⟨loM, hloM, hloMV⟩
  rcases ipv6_broadcast_nat_spec n hn with ⟨hiN, hhiN, hhiNV⟩
  rcases ipv6_broadcast_nat_spec m hm with ⟨hiM, hhiM, hhiMV⟩
  simp only [ipnet.Ipv6Net.Insts.IpnetIpnetContainsSharedAIpv6Net.contains,
    hloN, hloM, hhiN, hhiM, le6,
    hloNV, hloMV, hhiNV, hhiMV, bind_ok]
  by_cases h : CidrModel.lower 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val ≤
      CidrModel.lower 128 (CidrModel.ipv6Value m.addr) m.prefix_len.val <;> simp [h]

/-- The actual IPv4 address implementation decides membership of every address. -/
theorem ipv4_contains_addr_spec (n : ipnet.Ipv4Net)
    (a : core.net.ip_addr.Ipv4Addr) (hp : n.prefix_len.val ≤ 32) :
    ∃ out : Bool,
      ipnet.Ipv4Net.Insts.IpnetIpnetContainsSharedAIpv4Addr.contains n a = Result.ok out ∧
      (out = true ↔ CidrModel.member 32 (CidrModel.ipv4Value n.addr)
        n.prefix_len.val (CidrModel.ipv4Value a)) := by
  refine ⟨decide (CidrModel.lower 32 (CidrModel.ipv4Value n.addr) n.prefix_len.val ≤ CidrModel.ipv4Value a ∧
    CidrModel.ipv4Value a ≤ CidrModel.upper 32 (CidrModel.ipv4Value n.addr) n.prefix_len.val),
    ipv4_contains_addr_result n a hp, ?_⟩
  simp [CidrModel.member]

theorem ipv6_contains_addr_spec (n : ipnet.Ipv6Net)
    (a : core.net.ip_addr.Ipv6Addr) (hp : n.prefix_len.val ≤ 128) :
    ∃ out : Bool,
      ipnet.Ipv6Net.Insts.IpnetIpnetContainsSharedAIpv6Addr.contains n a = Result.ok out ∧
      (out = true ↔ CidrModel.member 128 (CidrModel.ipv6Value n.addr)
        n.prefix_len.val (CidrModel.ipv6Value a)) := by
  refine ⟨decide (CidrModel.lower 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val ≤ CidrModel.ipv6Value a ∧
    CidrModel.ipv6Value a ≤ CidrModel.upper 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val),
    ipv6_contains_addr_result n a hp, ?_⟩
  simp [CidrModel.member]

theorem ipv4_contains_net_spec (n m : ipnet.Ipv4Net)
    (hn : n.prefix_len.val ≤ 32) (hm : m.prefix_len.val ≤ 32) :
    ∃ out : Bool,
      ipnet.Ipv4Net.Insts.IpnetIpnetContainsSharedAIpv4Net.contains n m = Result.ok out ∧
      (out = true ↔ CidrModel.subset 32 (CidrModel.ipv4Value n.addr)
        n.prefix_len.val (CidrModel.ipv4Value m.addr) m.prefix_len.val) := by
  refine ⟨decide (CidrModel.lower 32 (CidrModel.ipv4Value n.addr) n.prefix_len.val ≤
    CidrModel.lower 32 (CidrModel.ipv4Value m.addr) m.prefix_len.val ∧
    CidrModel.upper 32 (CidrModel.ipv4Value m.addr) m.prefix_len.val ≤
    CidrModel.upper 32 (CidrModel.ipv4Value n.addr) n.prefix_len.val),
    ipv4_contains_net_result n m hn hm, ?_⟩
  simp [CidrModel.subset_iff_endpoints]

theorem ipv6_contains_net_spec (n m : ipnet.Ipv6Net)
    (hn : n.prefix_len.val ≤ 128) (hm : m.prefix_len.val ≤ 128) :
    ∃ out : Bool,
      ipnet.Ipv6Net.Insts.IpnetIpnetContainsSharedAIpv6Net.contains n m = Result.ok out ∧
      (out = true ↔ CidrModel.subset 128 (CidrModel.ipv6Value n.addr)
        n.prefix_len.val (CidrModel.ipv6Value m.addr) m.prefix_len.val) := by
  refine ⟨decide (CidrModel.lower 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val ≤
    CidrModel.lower 128 (CidrModel.ipv6Value m.addr) m.prefix_len.val ∧
    CidrModel.upper 128 (CidrModel.ipv6Value m.addr) m.prefix_len.val ≤
    CidrModel.upper 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val),
    ipv6_contains_net_result n m hn hm, ?_⟩
  simp [CidrModel.subset_iff_endpoints]

/-- Independent family, width and numeric observations used by the tagged CIDR model. -/
def netFamily : ipnet.IpNet → Nat
  | .V4 _ => 4
  | .V6 _ => 6

def netWidth : ipnet.IpNet → Nat
  | .V4 _ => 32
  | .V6 _ => 128

def netAddressValue : ipnet.IpNet → Nat
  | .V4 n => CidrModel.ipv4Value n.addr
  | .V6 n => CidrModel.ipv6Value n.addr

def netPrefix : ipnet.IpNet → Nat
  | .V4 n => n.prefix_len.val
  | .V6 n => n.prefix_len.val

def addressFamily : core.net.ip_addr.IpAddr → Nat
  | .V4 _ => 4
  | .V6 _ => 6

def addressValue : core.net.ip_addr.IpAddr → Nat
  | .V4 a => CidrModel.ipv4Value a
  | .V6 a => CidrModel.ipv6Value a

def taggedMember (n : ipnet.IpNet) (a : core.net.ip_addr.IpAddr) : Prop :=
  CidrModel.taggedMember (netFamily n) (netWidth n) (netAddressValue n)
    (netPrefix n) (addressFamily a, addressValue a)

def taggedSubset (n m : ipnet.IpNet) : Prop :=
  CidrModel.taggedSubset (netFamily n) (netWidth n) (netAddressValue n)
    (netPrefix n) (netFamily m) (netWidth m) (netAddressValue m) (netPrefix m)

theorem ip_contains_addr_spec (n : ipnet.IpNet) (a : core.net.ip_addr.IpAddr)
    (hn : match n with
      | .V4 v => v.prefix_len.val ≤ 32
      | .V6 v => v.prefix_len.val ≤ 128) :
    ∃ out : Bool,
      ipnet.IpNet.Insts.IpnetIpnetContainsSharedAIpAddr.contains n a = Result.ok out ∧
      (out = true ↔ taggedMember n a) := by
  cases n with
  | V4 v =>
    cases a with
    | V4 x =>
      rcases ipv4_contains_addr_spec v x hn with ⟨out, hr, hs⟩
      refine ⟨out, ?_, ?_⟩
      · simpa [ipnet.IpNet.Insts.IpnetIpnetContainsSharedAIpAddr.contains,
          ipnet.Ipv4Net.contains] using hr
      · simpa [taggedMember, netFamily, netWidth, netAddressValue,
          netPrefix, addressFamily, addressValue, CidrModel.taggedMember] using hs
    | V6 x =>
      refine ⟨false, rfl, ?_⟩
      simp [taggedMember, netFamily, addressFamily, CidrModel.taggedMember]
  | V6 v =>
    cases a with
    | V4 x =>
      refine ⟨false, rfl, ?_⟩
      simp [taggedMember, netFamily, addressFamily, CidrModel.taggedMember]
    | V6 x =>
      rcases ipv6_contains_addr_spec v x hn with ⟨out, hr, hs⟩
      refine ⟨out, ?_, ?_⟩
      · simpa [ipnet.IpNet.Insts.IpnetIpnetContainsSharedAIpAddr.contains,
          ipnet.Ipv6Net.contains] using hr
      · simpa [taggedMember, netFamily, netWidth, netAddressValue,
          netPrefix, addressFamily, addressValue, CidrModel.taggedMember] using hs

theorem ip_contains_net_spec (n m : ipnet.IpNet)
    (hn : match n with
      | .V4 v => v.prefix_len.val ≤ 32
      | .V6 v => v.prefix_len.val ≤ 128)
    (hm : match m with
      | .V4 v => v.prefix_len.val ≤ 32
      | .V6 v => v.prefix_len.val ≤ 128) :
    ∃ out : Bool,
      ipnet.IpNet.Insts.IpnetIpnetContainsSharedAIpNet.contains n m = Result.ok out ∧
      (out = true ↔ taggedSubset n m) := by
  cases n with
  | V4 v =>
    cases m with
    | V4 w =>
      rcases ipv4_contains_net_spec v w hn hm with ⟨out, hr, hs⟩
      refine ⟨out, ?_, ?_⟩
      · simpa [ipnet.IpNet.Insts.IpnetIpnetContainsSharedAIpNet.contains,
          ipnet.Ipv4Net.contains] using hr
      · simpa [taggedSubset, netFamily, netWidth, netAddressValue,
          netPrefix, CidrModel.tagged_subset_iff, CidrModel.subset_iff_endpoints] using hs
    | V6 w =>
      refine ⟨false, rfl, ?_⟩
      simp [taggedSubset, netFamily, CidrModel.tagged_subset_iff]
  | V6 v =>
    cases m with
    | V4 w =>
      refine ⟨false, rfl, ?_⟩
      simp [taggedSubset, netFamily, CidrModel.tagged_subset_iff]
    | V6 w =>
      rcases ipv6_contains_net_spec v w hn hm with ⟨out, hr, hs⟩
      refine ⟨out, ?_, ?_⟩
      · simpa [ipnet.IpNet.Insts.IpnetIpnetContainsSharedAIpNet.contains,
          ipnet.Ipv6Net.contains] using hr
      · simpa [taggedSubset, netFamily, netWidth, netAddressValue,
          netPrefix, CidrModel.tagged_subset_iff, CidrModel.subset_iff_endpoints] using hs

/-- Public `Ipv4Net::contains(&Ipv4Addr)` uses its selected trait instance. -/
theorem ipv4_public_contains_addr_spec (n : ipnet.Ipv4Net)
    (a : core.net.ip_addr.Ipv4Addr) (hp : n.prefix_len.val ≤ 32) :
    ∃ out : Bool,
      ipnet.Ipv4Net.contains ipnet.Ipv4Net.Insts.IpnetIpnetContainsSharedAIpv4Addr n a =
        Result.ok out ∧
      (out = true ↔ CidrModel.member 32 (CidrModel.ipv4Value n.addr)
        n.prefix_len.val (CidrModel.ipv4Value a)) := by
  rcases ipv4_contains_addr_spec n a hp with ⟨out, hr, hs⟩
  exact ⟨out, by simpa [ipnet.Ipv4Net.contains,
    ipnet.Ipv4Net.Insts.IpnetIpnetContainsSharedAIpv4Addr] using hr, hs⟩

theorem ipv6_public_contains_addr_spec (n : ipnet.Ipv6Net)
    (a : core.net.ip_addr.Ipv6Addr) (hp : n.prefix_len.val ≤ 128) :
    ∃ out : Bool,
      ipnet.Ipv6Net.contains ipnet.Ipv6Net.Insts.IpnetIpnetContainsSharedAIpv6Addr n a =
        Result.ok out ∧
      (out = true ↔ CidrModel.member 128 (CidrModel.ipv6Value n.addr)
        n.prefix_len.val (CidrModel.ipv6Value a)) := by
  rcases ipv6_contains_addr_spec n a hp with ⟨out, hr, hs⟩
  exact ⟨out, by simpa [ipnet.Ipv6Net.contains,
    ipnet.Ipv6Net.Insts.IpnetIpnetContainsSharedAIpv6Addr] using hr, hs⟩

theorem ipv4_public_contains_net_spec (n m : ipnet.Ipv4Net)
    (hn : n.prefix_len.val ≤ 32) (hm : m.prefix_len.val ≤ 32) :
    ∃ out : Bool,
      ipnet.Ipv4Net.contains ipnet.Ipv4Net.Insts.IpnetIpnetContainsSharedAIpv4Net n m =
        Result.ok out ∧
      (out = true ↔ CidrModel.subset 32 (CidrModel.ipv4Value n.addr)
        n.prefix_len.val (CidrModel.ipv4Value m.addr) m.prefix_len.val) := by
  rcases ipv4_contains_net_spec n m hn hm with ⟨out, hr, hs⟩
  exact ⟨out, by simpa [ipnet.Ipv4Net.contains,
    ipnet.Ipv4Net.Insts.IpnetIpnetContainsSharedAIpv4Net] using hr, hs⟩

theorem ipv6_public_contains_net_spec (n m : ipnet.Ipv6Net)
    (hn : n.prefix_len.val ≤ 128) (hm : m.prefix_len.val ≤ 128) :
    ∃ out : Bool,
      ipnet.Ipv6Net.contains ipnet.Ipv6Net.Insts.IpnetIpnetContainsSharedAIpv6Net n m =
        Result.ok out ∧
      (out = true ↔ CidrModel.subset 128 (CidrModel.ipv6Value n.addr)
        n.prefix_len.val (CidrModel.ipv6Value m.addr) m.prefix_len.val) := by
  rcases ipv6_contains_net_spec n m hn hm with ⟨out, hr, hs⟩
  exact ⟨out, by simpa [ipnet.Ipv6Net.contains,
    ipnet.Ipv6Net.Insts.IpnetIpnetContainsSharedAIpv6Net] using hr, hs⟩

/-- Aeneas omits these unused instance records. The sole field is fixed to the
    corresponding extracted method (LLBC trait impl 7, method 49). -/
def selectedIpContainsAddr : ipnet.Contains ipnet.IpNet core.net.ip_addr.IpAddr :=
  { contains := ipnet.IpNet.Insts.IpnetIpnetContainsSharedAIpAddr.contains }

/-- The corresponding extracted IpNet-to-IpNet method is LLBC impl 6, method 48. -/
def selectedIpContainsNet : ipnet.Contains ipnet.IpNet ipnet.IpNet :=
  { contains := ipnet.IpNet.Insts.IpnetIpnetContainsSharedAIpNet.contains }

theorem ip_public_contains_addr_spec (n : ipnet.IpNet)
    (a : core.net.ip_addr.IpAddr)
    (hn : match n with
      | .V4 v => v.prefix_len.val ≤ 32
      | .V6 v => v.prefix_len.val ≤ 128) :
    ∃ out : Bool,
      ipnet.IpNet.contains selectedIpContainsAddr n a =
        Result.ok out ∧ (out = true ↔ taggedMember n a) := by
  rcases ip_contains_addr_spec n a hn with ⟨out, hr, hs⟩
  exact ⟨out, by simpa [ipnet.IpNet.contains, selectedIpContainsAddr] using hr, hs⟩

theorem ip_public_contains_net_spec (n m : ipnet.IpNet)
    (hn : match n with
      | .V4 v => v.prefix_len.val ≤ 32
      | .V6 v => v.prefix_len.val ≤ 128)
    (hm : match m with
      | .V4 v => v.prefix_len.val ≤ 32
      | .V6 v => v.prefix_len.val ≤ 128) :
    ∃ out : Bool,
      ipnet.IpNet.contains selectedIpContainsNet n m =
        Result.ok out ∧ (out = true ↔ taggedSubset n m) := by
  rcases ip_contains_net_spec n m hn hm with ⟨out, hr, hs⟩
  exact ⟨out, by simpa [ipnet.IpNet.contains, selectedIpContainsNet] using hr, hs⟩

end ipnet
