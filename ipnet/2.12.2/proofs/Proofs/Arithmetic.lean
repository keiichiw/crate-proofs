module
public import Ipnet
public import Proofs.MaskMath
public import Proofs.AddressConversions
public import Proofs.NetworkMath

public section

open Aeneas Aeneas.Std

namespace ipnet

theorem u32_and_value (a m : U32) : (a &&& m).val = a.val &&& m.val := by
  change (a.bv &&& m.bv).toNat = a.bv.toNat &&& m.bv.toNat
  exact BitVec.toNat_and a.bv m.bv

theorem u32_or_value (a m : U32) : (a ||| m).val = a.val ||| m.val := by
  change (a.bv ||| m.bv).toNat = a.bv.toNat ||| m.bv.toNat
  exact BitVec.toNat_or a.bv m.bv

theorem u128_and_value (a m : U128) : (a &&& m).val = a.val &&& m.val := by
  change (a.bv &&& m.bv).toNat = a.bv.toNat &&& m.bv.toNat
  exact BitVec.toNat_and a.bv m.bv

theorem u128_or_value (a m : U128) : (a ||| m).val = a.val ||| m.val := by
  change (a.bv ||| m.bv).toNat = a.bv.toNat ||| m.bv.toNat
  exact BitVec.toNat_or a.bv m.bv

theorem max32_shiftLeft_value (s : Nat) (hs : s ≤ 32) :
    (core.num.U32.MAX.bv.shiftLeft s).toNat = 2 ^ 32 - 2 ^ s := by
  simpa [core.num.U32.MAX, U32.rMax] using MaskMath.max_shiftLeft_value 32 s hs

theorem max32_ushiftRight_value (p : Nat) (hp : p ≤ 32) :
    (core.num.U32.MAX.bv.ushiftRight p).toNat = 2 ^ (32 - p) - 1 := by
  simpa [core.num.U32.MAX, U32.rMax] using MaskMath.max_ushiftRight_value 32 p hp

theorem max128_shiftLeft_value (s : Nat) (hs : s ≤ 128) :
    (core.num.U128.MAX.bv.shiftLeft s).toNat = 2 ^ 128 - 2 ^ s := by
  simpa [core.num.U128.MAX, U128.rMax] using MaskMath.max_shiftLeft_value 128 s hs

theorem max128_ushiftRight_value (p : Nat) (hp : p ≤ 128) :
    (core.num.U128.MAX.bv.ushiftRight p).toNat = 2 ^ (128 - p) - 1 := by
  simpa [core.num.U128.MAX, U128.rMax] using MaskMath.max_ushiftRight_value 128 p hp

/-- The extracted checked shift succeeds at every in-range count, including
the boundary 31. The shift model itself rejects counts 32 and above. -/
theorem checked_shl_u32_spec (x rhs : U32) (h : rhs.val < 32) :
    core.num.U32.checked_shl x rhs =
      Result.ok (some ⟨x.bv.shiftLeft rhs.val⟩) := by
  simp [core.num.U32.checked_shl, core.num.U32.unchecked_shl,
    core.ub_checks.check_language_ub, core.ub_checks.check_language_ub.runtime,
    U32.shl, UScalar.shiftLeft_UScalar, UScalar.shiftLeft,
    core.num.U32.BITS, h]

theorem checked_shr_u32_spec (x rhs : U32) (h : rhs.val < 32) :
    core.num.U32.checked_shr x rhs =
      Result.ok (some ⟨x.bv.ushiftRight rhs.val⟩) := by
  simp [core.num.U32.checked_shr, core.num.U32.unchecked_shr,
    core.ub_checks.check_language_ub, core.ub_checks.check_language_ub.runtime,
    U32.shr, UScalar.shiftRight_UScalar, UScalar.shiftRight,
    core.num.U32.BITS, h]

theorem checked_shl_u128_spec (x : U128) (rhs : U32) (h : rhs.val < 128) :
    core.num.U128.checked_shl x rhs =
      Result.ok (some ⟨x.bv.shiftLeft rhs.val⟩) := by
  simp [core.num.U128.checked_shl, core.num.U128.unchecked_shl,
    core.ub_checks.check_language_ub, core.ub_checks.check_language_ub.runtime,
    U128.shl, UScalar.shiftLeft_UScalar, UScalar.shiftLeft,
    core.num.U128.BITS, h]

theorem checked_shr_u128_spec (x : U128) (rhs : U32) (h : rhs.val < 128) :
    core.num.U128.checked_shr x rhs =
      Result.ok (some ⟨x.bv.ushiftRight rhs.val⟩) := by
  simp [core.num.U128.checked_shr, core.num.U128.unchecked_shr,
    core.ub_checks.check_language_ub, core.ub_checks.check_language_ub.runtime,
    U128.shr, UScalar.shiftRight_UScalar, UScalar.shiftRight,
    core.num.U128.BITS, h]

/-- A valid IPv4 prefix computes a mask without arithmetic failure. The
resulting bitvector is exactly the maximum 32-bit word shifted by `32 - p`;
at `/0`, the checked shift returns `none` and the mask is zero. -/
theorem ipv4_netmask_u32_spec (n : ipnet.Ipv4Net)
    (hp : n.prefix_len.val ≤ 32) :
    ∃ mask : U32, ipnet.Ipv4Net.netmask_u32 n = Result.ok mask ∧
      mask = if n.prefix_len.val = 0 then 0#u32
        else ⟨core.num.U32.MAX.bv.shiftLeft (32 - n.prefix_len.val)⟩ := by
  let c : U32 := UScalar.cast .U32 n.prefix_len
  let s : U32 := ⟨BitVec.ofNat 32 (32 - n.prefix_len.val)⟩
  have hc : c.val = n.prefix_len.val := U8.cast_U32_val_eq n.prefix_len
  have hs : s.val = 32 - n.prefix_len.val := by
    change (BitVec.ofNat 32 (32 - n.prefix_len.val)).toNat = 32 - n.prefix_len.val
    rw [BitVec.toNat_ofNat]
    norm_num
    omega
  have hsub : (32#u32 - c : Result U32) = Result.ok s := by
    simp [HSub.hSub, UScalar.sub, hc, hp, s]
  by_cases hz : n.prefix_len.val = 0
  · have hshift : core.num.U32.checked_shl core.num.U32.MAX s = Result.ok none := by
      simp [core.num.U32.checked_shl, core.num.U32.BITS, hs, hz]
    refine ⟨0#u32, ?_, by simp [hz]⟩
    change (do
      let i ← core.num.U32.max_value
      let i1 ← lift c
      let i2 ← (32#u32 - i1 : Result U32)
      let o ← core.num.U32.checked_shl i i2
      Result.ok (core.option.Option.unwrap_or o 0#u32)) = Result.ok 0#u32
    simp [core.num.U32.max_value, lift, bind_ok, hsub, hshift,
      core.option.Option.unwrap_or]
  · have hlt : s.val < 32 := by omega
    have hshift := checked_shl_u32_spec core.num.U32.MAX s hlt
    refine ⟨⟨core.num.U32.MAX.bv.shiftLeft (32 - n.prefix_len.val)⟩, ?_, by simp [hz]⟩
    change (do
      let i ← core.num.U32.max_value
      let i1 ← lift c
      let i2 ← (32#u32 - i1 : Result U32)
      let o ← core.num.U32.checked_shl i i2
      Result.ok (core.option.Option.unwrap_or o 0#u32)) =
      Result.ok ⟨core.num.U32.MAX.bv.shiftLeft (32 - n.prefix_len.val)⟩
    simp [core.num.U32.max_value, lift, bind_ok, hsub, hshift, hs,
      core.option.Option.unwrap_or]

/-- The public IPv4 netmask API succeeds on all valid prefixes and returns
the network-order bytes of the precise shifted 32-bit mask. -/
theorem ipv4_netmask_spec (n : ipnet.Ipv4Net)
    (hp : n.prefix_len.val ≤ 32) :
    ∃ mask : core.net.ip_addr.Ipv4Addr,
      ipnet.Ipv4Net.netmask n = Result.ok mask ∧
      mask.octets = core.num.U32.to_be_bytes
        (if n.prefix_len.val = 0 then 0#u32
         else ⟨core.num.U32.MAX.bv.shiftLeft (32 - n.prefix_len.val)⟩) := by
  rcases ipv4_netmask_u32_spec n hp with ⟨word, hw, he⟩
  refine ⟨{ octets := core.num.U32.to_be_bytes word }, ?_, ?_⟩
  · simp [ipnet.Ipv4Net.netmask, core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from,
      core.net.ip_addr.Ipv4Addr.from_bits, lift, hw]
  · simp [he]

theorem ipv4_hostmask_u32_spec (n : ipnet.Ipv4Net)
    (hp : n.prefix_len.val ≤ 32) :
    ∃ mask : U32, ipnet.Ipv4Net.hostmask_u32 n = Result.ok mask ∧
      mask = if n.prefix_len.val = 32 then 0#u32
        else ⟨core.num.U32.MAX.bv.ushiftRight n.prefix_len.val⟩ := by
  let c : U32 := UScalar.cast .U32 n.prefix_len
  have hc : c.val = n.prefix_len.val := U8.cast_U32_val_eq n.prefix_len
  by_cases hz : n.prefix_len.val = 32
  · have hshift : core.num.U32.checked_shr core.num.U32.MAX c = Result.ok none := by
      simp [core.num.U32.checked_shr, core.num.U32.BITS, hc, hz]
    refine ⟨0#u32, ?_, by simp [hz]⟩
    change (do
      let i ← core.num.U32.max_value
      let i1 ← lift c
      let o ← core.num.U32.checked_shr i i1
      Result.ok (core.option.Option.unwrap_or o 0#u32)) = Result.ok 0#u32
    simp [core.num.U32.max_value, lift, bind_ok, hshift,
      core.option.Option.unwrap_or]
  · have hlt : c.val < 32 := by omega
    have hshift := checked_shr_u32_spec core.num.U32.MAX c hlt
    refine ⟨⟨core.num.U32.MAX.bv.ushiftRight n.prefix_len.val⟩, ?_, by simp [hz]⟩
    change (do
      let i ← core.num.U32.max_value
      let i1 ← lift c
      let o ← core.num.U32.checked_shr i i1
      Result.ok (core.option.Option.unwrap_or o 0#u32)) =
      Result.ok ⟨core.num.U32.MAX.bv.ushiftRight n.prefix_len.val⟩
    simp [core.num.U32.max_value, lift, bind_ok, hshift, hc,
      core.option.Option.unwrap_or]

theorem ipv4_hostmask_spec (n : ipnet.Ipv4Net)
    (hp : n.prefix_len.val ≤ 32) :
    ∃ mask : core.net.ip_addr.Ipv4Addr,
      ipnet.Ipv4Net.hostmask n = Result.ok mask ∧
      mask.octets = core.num.U32.to_be_bytes
        (if n.prefix_len.val = 32 then 0#u32
         else ⟨core.num.U32.MAX.bv.ushiftRight n.prefix_len.val⟩) := by
  rcases ipv4_hostmask_u32_spec n hp with ⟨word, hw, he⟩
  refine ⟨{ octets := core.num.U32.to_be_bytes word }, ?_, ?_⟩
  · simp [ipnet.Ipv4Net.hostmask, core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from,
      core.net.ip_addr.Ipv4Addr.from_bits, lift, hw]
  · simp [he]

theorem ipv6_netmask_u128_spec (n : ipnet.Ipv6Net)
    (hp : n.prefix_len.val ≤ 128) :
    ∃ mask : U128, ipnet.Ipv6Net.netmask_u128 n = Result.ok mask ∧
      mask = if n.prefix_len.val = 0 then 0#u128
        else ⟨core.num.U128.MAX.bv.shiftLeft (128 - n.prefix_len.val)⟩ := by
  let s8 : U8 := ⟨BitVec.ofNat 8 (128 - n.prefix_len.val)⟩
  let s : U32 := UScalar.cast .U32 s8
  have hs8 : s8.val = 128 - n.prefix_len.val := by
    change (BitVec.ofNat 8 (128 - n.prefix_len.val)).toNat = 128 - n.prefix_len.val
    rw [BitVec.toNat_ofNat]
    norm_num
    omega
  have hs : s.val = 128 - n.prefix_len.val := by
    rw [U8.cast_U32_val_eq, hs8]
  have hsub : (128#u8 - n.prefix_len : Result U8) = Result.ok s8 := by
    simp [HSub.hSub, UScalar.sub, hp, s8]
  by_cases hz : n.prefix_len.val = 0
  · have hshift : core.num.U128.checked_shl core.num.U128.MAX s = Result.ok none := by
      simp [core.num.U128.checked_shl, core.num.U128.BITS, hs, hz]
    refine ⟨0#u128, ?_, by simp [hz]⟩
    change (do
      let i ← core.num.U128.max_value
      let i1 ← (128#u8 - n.prefix_len : Result U8)
      let i2 ← lift (UScalar.cast .U32 i1)
      let o ← core.num.U128.checked_shl i i2
      let i3 ← core.num.U128.min_value
      Result.ok (core.option.Option.unwrap_or o i3)) = Result.ok 0#u128
    simp [core.num.U128.max_value, core.num.U128.min_value, lift, bind_ok,
      hsub, hshift, core.option.Option.unwrap_or, s]
  · have hlt : s.val < 128 := by omega
    have hshift := checked_shl_u128_spec core.num.U128.MAX s hlt
    refine ⟨⟨core.num.U128.MAX.bv.shiftLeft (128 - n.prefix_len.val)⟩, ?_, by simp [hz]⟩
    change (do
      let i ← core.num.U128.max_value
      let i1 ← (128#u8 - n.prefix_len : Result U8)
      let i2 ← lift (UScalar.cast .U32 i1)
      let o ← core.num.U128.checked_shl i i2
      let i3 ← core.num.U128.min_value
      Result.ok (core.option.Option.unwrap_or o i3)) =
      Result.ok ⟨core.num.U128.MAX.bv.shiftLeft (128 - n.prefix_len.val)⟩
    simp [core.num.U128.max_value, core.num.U128.min_value, lift, bind_ok,
      hsub, hshift, hs, core.option.Option.unwrap_or, s]

theorem ipv6_hostmask_u128_spec (n : ipnet.Ipv6Net)
    (hp : n.prefix_len.val ≤ 128) :
    ∃ mask : U128, ipnet.Ipv6Net.hostmask_u128 n = Result.ok mask ∧
      mask = if n.prefix_len.val = 128 then 0#u128
        else ⟨core.num.U128.MAX.bv.ushiftRight n.prefix_len.val⟩ := by
  let c : U32 := UScalar.cast .U32 n.prefix_len
  have hc : c.val = n.prefix_len.val := U8.cast_U32_val_eq n.prefix_len
  by_cases hz : n.prefix_len.val = 128
  · have hshift : core.num.U128.checked_shr core.num.U128.MAX c = Result.ok none := by
      simp [core.num.U128.checked_shr, core.num.U128.BITS, hc, hz]
    refine ⟨0#u128, ?_, by simp [hz]⟩
    change (do
      let i ← core.num.U128.max_value
      let i1 ← lift c
      let o ← core.num.U128.checked_shr i i1
      let i2 ← core.num.U128.min_value
      Result.ok (core.option.Option.unwrap_or o i2)) = Result.ok 0#u128
    simp [core.num.U128.max_value, core.num.U128.min_value, lift, bind_ok,
      hshift, core.option.Option.unwrap_or]
  · have hlt : c.val < 128 := by omega
    have hshift := checked_shr_u128_spec core.num.U128.MAX c hlt
    refine ⟨⟨core.num.U128.MAX.bv.ushiftRight n.prefix_len.val⟩, ?_, by simp [hz]⟩
    change (do
      let i ← core.num.U128.max_value
      let i1 ← lift c
      let o ← core.num.U128.checked_shr i i1
      let i2 ← core.num.U128.min_value
      Result.ok (core.option.Option.unwrap_or o i2)) =
      Result.ok ⟨core.num.U128.MAX.bv.ushiftRight n.prefix_len.val⟩
    simp [core.num.U128.max_value, core.num.U128.min_value, lift, bind_ok,
      hshift, hc, core.option.Option.unwrap_or]

theorem ipv4_netmask_u32_nat_spec (n : ipnet.Ipv4Net)
    (hp : n.prefix_len.val ≤ 32) :
    ∃ mask : U32, ipnet.Ipv4Net.netmask_u32 n = Result.ok mask ∧
      mask.val = 2 ^ 32 - 2 ^ (32 - n.prefix_len.val) := by
  rcases ipv4_netmask_u32_spec n hp with ⟨mask, hm, he⟩
  refine ⟨mask, hm, ?_⟩
  by_cases hz : n.prefix_len.val = 0
  · simp [he, hz]
  · rw [he, ite_eq_right hz]
    exact max32_shiftLeft_value _ (by omega)

theorem ipv4_hostmask_u32_nat_spec (n : ipnet.Ipv4Net)
    (hp : n.prefix_len.val ≤ 32) :
    ∃ mask : U32, ipnet.Ipv4Net.hostmask_u32 n = Result.ok mask ∧
      mask.val = 2 ^ (32 - n.prefix_len.val) - 1 := by
  rcases ipv4_hostmask_u32_spec n hp with ⟨mask, hm, he⟩
  refine ⟨mask, hm, ?_⟩
  by_cases hz : n.prefix_len.val = 32
  · simp [he, hz]
  · rw [he, ite_eq_right hz]
    exact max32_ushiftRight_value _ hp

theorem ipv6_netmask_u128_nat_spec (n : ipnet.Ipv6Net)
    (hp : n.prefix_len.val ≤ 128) :
    ∃ mask : U128, ipnet.Ipv6Net.netmask_u128 n = Result.ok mask ∧
      mask.val = 2 ^ 128 - 2 ^ (128 - n.prefix_len.val) := by
  rcases ipv6_netmask_u128_spec n hp with ⟨mask, hm, he⟩
  refine ⟨mask, hm, ?_⟩
  by_cases hz : n.prefix_len.val = 0
  · simp [he, hz]
  · rw [he, ite_eq_right hz]
    exact max128_shiftLeft_value _ (by omega)

theorem ipv6_hostmask_u128_nat_spec (n : ipnet.Ipv6Net)
    (hp : n.prefix_len.val ≤ 128) :
    ∃ mask : U128, ipnet.Ipv6Net.hostmask_u128 n = Result.ok mask ∧
      mask.val = 2 ^ (128 - n.prefix_len.val) - 1 := by
  rcases ipv6_hostmask_u128_spec n hp with ⟨mask, hm, he⟩
  refine ⟨mask, hm, ?_⟩
  by_cases hz : n.prefix_len.val = 128
  · simp [he, hz]
  · rw [he, ite_eq_right hz]
    exact max128_ushiftRight_value _ hp

/-- The public IPv4 netmask has the exact independent network-order integer
value of a CIDR prefix mask for every valid prefix. -/
theorem ipv4_netmask_nat_spec (n : ipnet.Ipv4Net)
    (hp : n.prefix_len.val ≤ 32) :
    ∃ out : core.net.ip_addr.Ipv4Addr,
      ipnet.Ipv4Net.netmask n = Result.ok out ∧
      CidrModel.ipv4Value out = 2 ^ 32 - 2 ^ (32 - n.prefix_len.val) := by
  rcases ipv4_netmask_u32_nat_spec n hp with ⟨word, hw, hval⟩
  rcases AddressConversions.ipv4_from_u32_spec word with ⟨out, hout, houtval⟩
  refine ⟨out, ?_, ?_⟩
  · simpa only [ipnet.Ipv4Net.netmask, hw, bind_ok] using hout
  · simpa [hval] using houtval

theorem ipv4_hostmask_nat_spec (n : ipnet.Ipv4Net)
    (hp : n.prefix_len.val ≤ 32) :
    ∃ out : core.net.ip_addr.Ipv4Addr,
      ipnet.Ipv4Net.hostmask n = Result.ok out ∧
      CidrModel.ipv4Value out = 2 ^ (32 - n.prefix_len.val) - 1 := by
  rcases ipv4_hostmask_u32_nat_spec n hp with ⟨word, hw, hval⟩
  rcases AddressConversions.ipv4_from_u32_spec word with ⟨out, hout, houtval⟩
  refine ⟨out, ?_, ?_⟩
  · simpa only [ipnet.Ipv4Net.hostmask, hw, bind_ok] using hout
  · simpa [hval] using houtval

theorem ipv6_netmask_nat_spec (n : ipnet.Ipv6Net)
    (hp : n.prefix_len.val ≤ 128) :
    ∃ out : core.net.ip_addr.Ipv6Addr,
      ipnet.Ipv6Net.netmask n = Result.ok out ∧
      CidrModel.ipv6Value out = 2 ^ 128 - 2 ^ (128 - n.prefix_len.val) := by
  rcases ipv6_netmask_u128_nat_spec n hp with ⟨word, hw, hval⟩
  rcases AddressConversions.ipv6_from_u128_spec word with ⟨out, hout, houtval⟩
  refine ⟨out, ?_, ?_⟩
  · simpa only [ipnet.Ipv6Net.netmask, hw, bind_ok, core.convert.IntoFrom.into,
      core.net.ip_addr.Ipv6Addr.Insts.CoreConvertFromU128] using hout
  · simpa [hval] using houtval

theorem ipv6_hostmask_nat_spec (n : ipnet.Ipv6Net)
    (hp : n.prefix_len.val ≤ 128) :
    ∃ out : core.net.ip_addr.Ipv6Addr,
      ipnet.Ipv6Net.hostmask n = Result.ok out ∧
      CidrModel.ipv6Value out = 2 ^ (128 - n.prefix_len.val) - 1 := by
  rcases ipv6_hostmask_u128_nat_spec n hp with ⟨word, hw, hval⟩
  rcases AddressConversions.ipv6_from_u128_spec word with ⟨out, hout, houtval⟩
  refine ⟨out, ?_, ?_⟩
  · simpa only [ipnet.Ipv6Net.hostmask, hw, bind_ok, core.convert.IntoFrom.into,
      core.net.ip_addr.Ipv6Addr.Insts.CoreConvertFromU128] using hout
  · simpa [hval] using houtval

theorem ip_netmask_nat_spec (n : ipnet.IpNet)
    (hp : match n with
      | .V4 v => v.prefix_len.val ≤ 32
      | .V6 v => v.prefix_len.val ≤ 128) :
    ∃ out : core.net.ip_addr.IpAddr,
      ipnet.IpNet.netmask n = Result.ok out ∧
      match n with
      | .V4 v => ∃ a, out = .V4 a ∧
          CidrModel.ipv4Value a = 2 ^ 32 - 2 ^ (32 - v.prefix_len.val)
      | .V6 v => ∃ a, out = .V6 a ∧
          CidrModel.ipv6Value a = 2 ^ 128 - 2 ^ (128 - v.prefix_len.val) := by
  cases n with
  | V4 v =>
    rcases ipv4_netmask_nat_spec v hp with ⟨a, ha, hv⟩
    refine ⟨.V4 a, ?_, ⟨a, rfl, hv⟩⟩
    simp [ipnet.IpNet.netmask, ha]
  | V6 v =>
    rcases ipv6_netmask_nat_spec v hp with ⟨a, ha, hv⟩
    refine ⟨.V6 a, ?_, ⟨a, rfl, hv⟩⟩
    simp [ipnet.IpNet.netmask, ha]

theorem ip_hostmask_nat_spec (n : ipnet.IpNet)
    (hp : match n with
      | .V4 v => v.prefix_len.val ≤ 32
      | .V6 v => v.prefix_len.val ≤ 128) :
    ∃ out : core.net.ip_addr.IpAddr,
      ipnet.IpNet.hostmask n = Result.ok out ∧
      match n with
      | .V4 v => ∃ a, out = .V4 a ∧
          CidrModel.ipv4Value a = 2 ^ (32 - v.prefix_len.val) - 1
      | .V6 v => ∃ a, out = .V6 a ∧
          CidrModel.ipv6Value a = 2 ^ (128 - v.prefix_len.val) - 1 := by
  cases n with
  | V4 v =>
    rcases ipv4_hostmask_nat_spec v hp with ⟨a, ha, hv⟩
    refine ⟨.V4 a, ?_, ⟨a, rfl, hv⟩⟩
    simp [ipnet.IpNet.hostmask, ha]
  | V6 v =>
    rcases ipv6_hostmask_nat_spec v hp with ⟨a, ha, hv⟩
    refine ⟨.V6 a, ?_, ⟨a, rfl, hv⟩⟩
    simp [ipnet.IpNet.hostmask, ha]

theorem ipv4_network_bitwise_spec (n : ipnet.Ipv4Net)
    (hp : n.prefix_len.val ≤ 32) :
    ∃ out : core.net.ip_addr.Ipv4Addr,
      ipnet.Ipv4Net.network n = Result.ok out ∧
      CidrModel.ipv4Value out =
        CidrModel.ipv4Value n.addr &&& (2 ^ 32 - 2 ^ (32 - n.prefix_len.val)) := by
  rcases AddressConversions.ipv4_into_u32_spec n.addr with ⟨a, ha, hav⟩
  rcases ipv4_netmask_u32_nat_spec n hp with ⟨m, hm, hmv⟩
  rcases AddressConversions.ipv4_from_u32_spec (a &&& m) with ⟨out, hout, houtv⟩
  refine ⟨out, ?_, ?_⟩
  · simpa [ipnet.Ipv4Net.network, ha, hm, lift] using hout
  · rw [houtv, u32_and_value, hav, hmv]

theorem ipv4_broadcast_bitwise_spec (n : ipnet.Ipv4Net)
    (hp : n.prefix_len.val ≤ 32) :
    ∃ out : core.net.ip_addr.Ipv4Addr,
      ipnet.Ipv4Net.broadcast n = Result.ok out ∧
      CidrModel.ipv4Value out =
        CidrModel.ipv4Value n.addr ||| (2 ^ (32 - n.prefix_len.val) - 1) := by
  rcases AddressConversions.ipv4_into_u32_spec n.addr with ⟨a, ha, hav⟩
  rcases ipv4_hostmask_u32_nat_spec n hp with ⟨m, hm, hmv⟩
  rcases AddressConversions.ipv4_from_u32_spec (a ||| m) with ⟨out, hout, houtv⟩
  refine ⟨out, ?_, ?_⟩
  · simpa [ipnet.Ipv4Net.broadcast, ha, hm, lift] using hout
  · rw [houtv, u32_or_value, hav, hmv]

theorem ipv6_network_bitwise_spec (n : ipnet.Ipv6Net)
    (hp : n.prefix_len.val ≤ 128) :
    ∃ out : core.net.ip_addr.Ipv6Addr,
      ipnet.Ipv6Net.network n = Result.ok out ∧
      CidrModel.ipv6Value out =
        CidrModel.ipv6Value n.addr &&& (2 ^ 128 - 2 ^ (128 - n.prefix_len.val)) := by
  rcases AddressConversions.ipv6_into_u128_spec n.addr with ⟨a, ha, hav⟩
  rcases ipv6_netmask_u128_nat_spec n hp with ⟨m, hm, hmv⟩
  rcases AddressConversions.ipv6_from_u128_spec (a &&& m) with ⟨out, hout, houtv⟩
  refine ⟨out, ?_, ?_⟩
  · simpa [ipnet.Ipv6Net.network, ha, hm, lift, core.convert.IntoFrom.into,
      core.net.ip_addr.Ipv6Addr.Insts.CoreConvertFromU128] using hout
  · rw [houtv, u128_and_value, hav, hmv]

theorem ipv6_broadcast_bitwise_spec (n : ipnet.Ipv6Net)
    (hp : n.prefix_len.val ≤ 128) :
    ∃ out : core.net.ip_addr.Ipv6Addr,
      ipnet.Ipv6Net.broadcast n = Result.ok out ∧
      CidrModel.ipv6Value out =
        CidrModel.ipv6Value n.addr ||| (2 ^ (128 - n.prefix_len.val) - 1) := by
  rcases AddressConversions.ipv6_into_u128_spec n.addr with ⟨a, ha, hav⟩
  rcases ipv6_hostmask_u128_nat_spec n hp with ⟨m, hm, hmv⟩
  rcases AddressConversions.ipv6_from_u128_spec (a ||| m) with ⟨out, hout, houtv⟩
  refine ⟨out, ?_, ?_⟩
  · simpa [ipnet.Ipv6Net.broadcast, ha, hm, lift, core.convert.IntoFrom.into,
      core.net.ip_addr.Ipv6Addr.Insts.CoreConvertFromU128] using hout
  · rw [houtv, u128_or_value, hav, hmv]

theorem ipv4_network_nat_spec (n : ipnet.Ipv4Net)
    (hp : n.prefix_len.val ≤ 32) :
    ∃ out : core.net.ip_addr.Ipv4Addr,
      ipnet.Ipv4Net.network n = Result.ok out ∧
      CidrModel.ipv4Value out =
        CidrModel.lower 32 (CidrModel.ipv4Value n.addr) n.prefix_len.val := by
  rcases ipv4_network_bitwise_spec n hp with ⟨out, hr, hv⟩
  refine ⟨out, hr, ?_⟩
  rw [hv]
  exact NetworkMath.and_netmask_eq_lower 32 (CidrModel.ipv4Value n.addr)
    n.prefix_len.val hp (CidrModel.ipv4Value_bound n.addr)

theorem ipv4_broadcast_nat_spec (n : ipnet.Ipv4Net)
    (hp : n.prefix_len.val ≤ 32) :
    ∃ out : core.net.ip_addr.Ipv4Addr,
      ipnet.Ipv4Net.broadcast n = Result.ok out ∧
      CidrModel.ipv4Value out =
        CidrModel.upper 32 (CidrModel.ipv4Value n.addr) n.prefix_len.val := by
  rcases ipv4_broadcast_bitwise_spec n hp with ⟨out, hr, hv⟩
  refine ⟨out, hr, ?_⟩
  rw [hv]
  exact NetworkMath.or_hostmask_eq_upper 32 (CidrModel.ipv4Value n.addr) n.prefix_len.val

theorem ipv6_network_nat_spec (n : ipnet.Ipv6Net)
    (hp : n.prefix_len.val ≤ 128) :
    ∃ out : core.net.ip_addr.Ipv6Addr,
      ipnet.Ipv6Net.network n = Result.ok out ∧
      CidrModel.ipv6Value out =
        CidrModel.lower 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val := by
  rcases ipv6_network_bitwise_spec n hp with ⟨out, hr, hv⟩
  refine ⟨out, hr, ?_⟩
  rw [hv]
  exact NetworkMath.and_netmask_eq_lower 128 (CidrModel.ipv6Value n.addr)
    n.prefix_len.val hp (CidrModel.ipv6Value_bound n.addr)

theorem ipv6_broadcast_nat_spec (n : ipnet.Ipv6Net)
    (hp : n.prefix_len.val ≤ 128) :
    ∃ out : core.net.ip_addr.Ipv6Addr,
      ipnet.Ipv6Net.broadcast n = Result.ok out ∧
      CidrModel.ipv6Value out =
        CidrModel.upper 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val := by
  rcases ipv6_broadcast_bitwise_spec n hp with ⟨out, hr, hv⟩
  refine ⟨out, hr, ?_⟩
  rw [hv]
  exact NetworkMath.or_hostmask_eq_upper 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val

theorem ip_network_nat_spec (n : ipnet.IpNet)
    (hp : match n with
      | .V4 v => v.prefix_len.val ≤ 32
      | .V6 v => v.prefix_len.val ≤ 128) :
    ∃ out : core.net.ip_addr.IpAddr,
      ipnet.IpNet.network n = Result.ok out ∧
      match n with
      | .V4 v => ∃ a, out = .V4 a ∧
          CidrModel.ipv4Value a =
            CidrModel.lower 32 (CidrModel.ipv4Value v.addr) v.prefix_len.val
      | .V6 v => ∃ a, out = .V6 a ∧
          CidrModel.ipv6Value a =
            CidrModel.lower 128 (CidrModel.ipv6Value v.addr) v.prefix_len.val := by
  cases n with
  | V4 v =>
    rcases ipv4_network_nat_spec v hp with ⟨a, ha, hv⟩
    refine ⟨.V4 a, ?_, ⟨a, rfl, hv⟩⟩
    simp [ipnet.IpNet.network, ha]
  | V6 v =>
    rcases ipv6_network_nat_spec v hp with ⟨a, ha, hv⟩
    refine ⟨.V6 a, ?_, ⟨a, rfl, hv⟩⟩
    simp [ipnet.IpNet.network, ha]

theorem ip_broadcast_nat_spec (n : ipnet.IpNet)
    (hp : match n with
      | .V4 v => v.prefix_len.val ≤ 32
      | .V6 v => v.prefix_len.val ≤ 128) :
    ∃ out : core.net.ip_addr.IpAddr,
      ipnet.IpNet.broadcast n = Result.ok out ∧
      match n with
      | .V4 v => ∃ a, out = .V4 a ∧
          CidrModel.ipv4Value a =
            CidrModel.upper 32 (CidrModel.ipv4Value v.addr) v.prefix_len.val
      | .V6 v => ∃ a, out = .V6 a ∧
          CidrModel.ipv6Value a =
            CidrModel.upper 128 (CidrModel.ipv6Value v.addr) v.prefix_len.val := by
  cases n with
  | V4 v =>
    rcases ipv4_broadcast_nat_spec v hp with ⟨a, ha, hv⟩
    refine ⟨.V4 a, ?_, ⟨a, rfl, hv⟩⟩
    simp [ipnet.IpNet.broadcast, ha]
  | V6 v =>
    rcases ipv6_broadcast_nat_spec v hp with ⟨a, ha, hv⟩
    refine ⟨.V6 a, ?_, ⟨a, rfl, hv⟩⟩
    simp [ipnet.IpNet.broadcast, ha]

theorem ipv4_trunc_nat_spec (n : ipnet.Ipv4Net)
    (hp : n.prefix_len.val ≤ 32) :
    ∃ out : ipnet.Ipv4Net,
      ipnet.Ipv4Net.trunc n = Result.ok out ∧
      out.prefix_len = n.prefix_len ∧
      CidrModel.ipv4Value out.addr =
        CidrModel.lower 32 (CidrModel.ipv4Value n.addr) n.prefix_len.val := by
  rcases ipv4_network_nat_spec n hp with ⟨a, ha, hv⟩
  refine ⟨{ addr := a, prefix_len := n.prefix_len }, ?_, rfl, hv⟩
  have hnot : ¬ 32 < n.prefix_len.val := by omega
  simp [ipnet.Ipv4Net.trunc, ha, ipnet.Ipv4Net.new,
    core.result.Result.unwrap_without_debug, hnot]

theorem ipv6_trunc_nat_spec (n : ipnet.Ipv6Net)
    (hp : n.prefix_len.val ≤ 128) :
    ∃ out : ipnet.Ipv6Net,
      ipnet.Ipv6Net.trunc n = Result.ok out ∧
      out.prefix_len = n.prefix_len ∧
      CidrModel.ipv6Value out.addr =
        CidrModel.lower 128 (CidrModel.ipv6Value n.addr) n.prefix_len.val := by
  rcases ipv6_network_nat_spec n hp with ⟨a, ha, hv⟩
  refine ⟨{ addr := a, prefix_len := n.prefix_len }, ?_, rfl, hv⟩
  have hnot : ¬ 128 < n.prefix_len.val := by omega
  simp [ipnet.Ipv6Net.trunc, ha, ipnet.Ipv6Net.new,
    core.result.Result.unwrap_without_debug, hnot]

theorem ip_trunc_nat_spec (n : ipnet.IpNet)
    (hp : match n with
      | .V4 v => v.prefix_len.val ≤ 32
      | .V6 v => v.prefix_len.val ≤ 128) :
    ∃ out : ipnet.IpNet,
      ipnet.IpNet.trunc n = Result.ok out ∧
      match n with
      | .V4 v => ∃ t, out = .V4 t ∧ t.prefix_len = v.prefix_len ∧
          CidrModel.ipv4Value t.addr =
            CidrModel.lower 32 (CidrModel.ipv4Value v.addr) v.prefix_len.val
      | .V6 v => ∃ t, out = .V6 t ∧ t.prefix_len = v.prefix_len ∧
          CidrModel.ipv6Value t.addr =
            CidrModel.lower 128 (CidrModel.ipv6Value v.addr) v.prefix_len.val := by
  cases n with
  | V4 v =>
    rcases ipv4_trunc_nat_spec v hp with ⟨t, ht, hp', hv⟩
    refine ⟨.V4 t, ?_, ⟨t, rfl, hp', hv⟩⟩
    simp [ipnet.IpNet.trunc, ht]
  | V6 v =>
    rcases ipv6_trunc_nat_spec v hp with ⟨t, ht, hp', hv⟩
    refine ⟨.V6 t, ?_, ⟨t, rfl, hp', hv⟩⟩
    simp [ipnet.IpNet.trunc, ht]
end ipnet
