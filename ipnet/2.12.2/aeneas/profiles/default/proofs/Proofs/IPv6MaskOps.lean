module
public import Proofs.IPv6MaskMath
public import Proofs.AddressConversions
public import Proofs.Arithmetic

public section
open Aeneas Aeneas.Std Result
namespace IPv6MaskOps
theorem prefix_bound (x : U128) :
    (core.num.U128.leading_zeros (~~~x)).val ≤ 128 := by
  rw [IPv6MaskMath.lz_val]
  split <;> omega
private theorem parser_shape (m : ipnet.core.net.ip_addr.Ipv6Addr) :
    ∃ x, ipnet.U128.Insts.CoreConvertFromIpv6Addr.from m = Result.ok x ∧
      x.val = CidrModel.ipv6Value m := by
  exact AddressConversions.ipv6_into_u128_spec m
theorem shift_zero_iff (x : U128) :
    let p := core.num.U128.leading_zeros (~~~x)
    ∃ o, ipnet.core.num.U128.checked_shl x p = Result.ok o ∧
      (core.option.Option.unwrap_or o 0#u128 = 0#u128 ↔
        (x.val * 2 ^ p.val) % 2 ^ 128 = 0) := by
  intro p
  have hp := prefix_bound x
  change p.val ≤ 128 at hp
  by_cases hlt : p.val < 128
  · refine ⟨some ⟨x.bv.shiftLeft p.val⟩, ?_, ?_⟩
    · exact ipnet.checked_shl_u128_spec x p hlt
    · simp only [core.option.Option.unwrap_or]
      change ((⟨x.bv.shiftLeft p.val⟩ : U128) = 0#u128 ↔
        (x.val * 2 ^ p.val) % 2 ^ 128 = 0)
      constructor
      · intro h
        have hv := congrArg UScalar.val h
        change (x.bv.shiftLeft p.val).toNat = 0 at hv
        simpa [BitVec.shiftLeft_eq, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] using hv
      · intro h
        apply congrArg UScalar.mk
        apply BitVec.eq_of_toNat_eq
        simpa [BitVec.shiftLeft_eq, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] using h
  · have heq : p.val = 128 := by omega
    refine ⟨none, ?_, ?_⟩
    · simp [ipnet.core.num.U128.checked_shl, core.num.U128.BITS, heq]
    · simp [core.option.Option.unwrap_or, heq]
def validMask (m : ipnet.core.net.ip_addr.Ipv6Addr) (p : Nat) : Prop :=
  p ≤ 128 ∧ CidrModel.ipv6Value m = 2 ^ 128 - 2 ^ (128-p)

theorem candidate_spec (m : ipnet.core.net.ip_addr.Ipv6Addr) :
    ∃ p : U8, p.val ≤ 128 ∧
      (validMask m p.val →
        ipnet.mask.ipv6_mask_to_prefix m = Result.ok (.Ok p)) ∧
      (¬validMask m p.val →
        ipnet.mask.ipv6_mask_to_prefix m = Result.ok (.Err ())) ∧
      (∀ q : U8, validMask m q.val → q = p) := by
  classical
  rcases parser_shape m with ⟨x, hx, hxv⟩
  let pu := core.num.U128.leading_zeros (~~~x)
  let p : U8 := UScalar.cast .U8 pu
  have hpu : pu.val ≤ 128 := prefix_bound x
  have hpv : p.val = pu.val := by
    simp [p, UScalar.cast_val_eq]
    omega
  rcases shift_zero_iff x with ⟨o, ho, hzero⟩
  have hnum : (x.val * 2 ^ pu.val) % 2 ^ 128 = 0 ↔
      validMask m p.val := by
    have hh := IPv6MaskMath.mask_numeric_iff x
    dsimp at hh
    change (x.val * 2 ^ pu.val) % 2 ^ 128 = 0 ↔
      x.val = 2 ^ 128 - 2 ^ (128-pu.val) at hh
    simp only [validMask, hpv, hpu, true_and, ← hxv]
    exact hh
  refine ⟨p, by omega, ?_, ?_, ?_⟩
  · intro hm
    have hs : core.option.Option.unwrap_or o 0#u128 = 0#u128 :=
      hzero.mpr (hnum.mpr hm)
    simp [ipnet.mask.ipv6_mask_to_prefix, hx, ipnet.core.num.U128.leading_ones,
      ho, hs, lift, bind_ok, p, pu]
  · intro hm
    have hs : core.option.Option.unwrap_or o 0#u128 ≠ 0#u128 := by
      intro hs
      exact hm (hnum.mp (hzero.mp hs))
    simp [ipnet.mask.ipv6_mask_to_prefix, hx, ipnet.core.num.U128.leading_ones,
      ho, hs, lift, bind_ok]
  · intro q hq
    have hprefix := IPv6MaskMath.valid_mask_prefix x q.val hq.1
      (by simpa only [← hxv] using hq.2)
    apply UScalar.eq_of_val_eq
    change pu.val = q.val at hprefix
    omega

/-- The generated parser returns a normal outer result, accepts precisely the
    contiguous masks, and rejects every other 128-bit pattern. -/
theorem ipv6_mask_to_prefix_spec (m : ipnet.core.net.ip_addr.Ipv6Addr) :
    ∃ out : core.result.Result U8 ipnet.ipnet.PrefixLenError,
      ipnet.mask.ipv6_mask_to_prefix m = Result.ok out ∧
      (∀ q : U8, out = .Ok q ↔ validMask m q.val) ∧
      (out = .Err () ↔ ¬∃ q : U8, validMask m q.val) := by
  rcases candidate_spec m with ⟨p, hp, hyes, hno, hunique⟩
  by_cases hv : validMask m p.val
  · refine ⟨.Ok p, hyes hv, ?_, ?_⟩
    · intro q
      constructor
      · intro h
        cases h
        exact hv
      · intro h
        have he := hunique q h
        simp [he]
    · constructor
      · intro h
        cases h
      · intro h
        exact False.elim (h ⟨p, hv⟩)
  · refine ⟨.Err (), hno hv, ?_, ?_⟩
    · intro q
      constructor
      · intro h
        cases h
      · intro h
        have he := hunique q h
        exact False.elim (hv (he ▸ h))
    · constructor
      · intro _ ⟨q,hq⟩
        have he := hunique q hq
        exact hv (he ▸ hq)
      · intro _
        rfl

/-- `with_netmask` stores the original address and accepts exactly the masks
    parsed as valid CIDR prefixes. -/
theorem with_netmask_spec (ip m : ipnet.core.net.ip_addr.Ipv6Addr) :
    ∃ out : core.result.Result ipnet.ipnet.Ipv6Net ipnet.ipnet.PrefixLenError,
      ipnet.ipnet.Ipv6Net.with_netmask ip m = Result.ok out ∧
      (∀ q : U8,
        out = .Ok { addr := ip, prefix_len := q } ↔ validMask m q.val) ∧
      (out = .Err () ↔ ¬∃ q : U8, validMask m q.val) := by
  rcases ipv6_mask_to_prefix_spec m with ⟨parsed, hparsed, hok, herr⟩
  cases parsed with
  | Ok p =>
    have hv : validMask m p.val := (hok p).mp rfl
    have hp : p.val ≤ 128 := hv.1
    let net : ipnet.ipnet.Ipv6Net := { addr := ip, prefix_len := p }
    have hnet : ipnet.ipnet.Ipv6Net.with_netmask ip m = Result.ok (.Ok net) := by
      simp [ipnet.ipnet.Ipv6Net.with_netmask, hparsed, ipnet.ipnet.Ipv6Net.new,
        core.result.Result.Insts.CoreOpsTry.branch, hp, net]
    refine ⟨.Ok net, hnet, ?_, ?_⟩
    · intro q
      constructor
      · intro he
        have hnete : net = { addr := ip, prefix_len := q } :=
          core.result.Result.Ok.inj he
        have hpeq : p = q := by
          have := congrArg (fun n : ipnet.ipnet.Ipv6Net => n.prefix_len) hnete
          simpa [net] using this
        exact (hok q).mp (by simp [hpeq])
      · intro hq
        have he : p = q := by
          have he1 : core.result.Result.Ok p = core.result.Result.Ok q :=
            (hok q).mpr hq
          exact core.result.Result.Ok.inj he1
        simp [net, he]
    · constructor
      · intro he
        cases he
      · intro hn
        exact False.elim (hn ⟨p,hv⟩)
  | Err e =>
    have hn : ¬∃ q : U8, validMask m q.val := (herr).mp rfl
    have hnet : ipnet.ipnet.Ipv6Net.with_netmask ip m = Result.ok (.Err ()) := by
      simp [ipnet.ipnet.Ipv6Net.with_netmask, hparsed,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    refine ⟨.Err (), hnet, ?_, ?_⟩
    · intro q
      constructor
      · intro he
        cases he
      · intro hq
        exact False.elim (hn ⟨q,hq⟩)
    · simp [hn]
end IPv6MaskOps
