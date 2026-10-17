module
public import Proofs.IPv4MaskOps
public import Proofs.IPv6MaskOps
public import Proofs.Core

public section
open Aeneas Aeneas.Std Result
namespace TaggedMask

def validMask (m : ipnet.core.net.ip_addr.IpAddr) (p : Nat) : Prop :=
  match m with
  | .V4 a => IPv4MaskOps.validMask a p
  | .V6 a => IPv6MaskOps.validMask a p

def addressWidth (ip : ipnet.core.net.ip_addr.IpAddr) : Nat :=
  match ip with
  | .V4 _ => 32
  | .V6 _ => 128

def expectedNet (ip : ipnet.core.net.ip_addr.IpAddr) (p : U8) : ipnet.ipnet.IpNet :=
  match ip with
  | .V4 a => .V4 { addr := a, prefix_len := p }
  | .V6 a => .V6 { addr := a, prefix_len := p }

theorem candidate (m : ipnet.core.net.ip_addr.IpAddr) :
    ∃ p : U8,
      (validMask m p.val → ipnet.mask.ip_mask_to_prefix m = Result.ok (.Ok p)) ∧
      (¬ validMask m p.val → ipnet.mask.ip_mask_to_prefix m = Result.ok (.Err ())) ∧
      (∀ q : U8, validMask m q.val → q = p) := by
  cases m with
  | V4 a =>
    rcases IPv4MaskOps.candidate_spec a with ⟨p, _, hy, hn, hu⟩
    refine ⟨p, ?_, ?_, ?_⟩
    · intro h; simpa only [validMask, ipnet.mask.ip_mask_to_prefix] using hy h
    · intro h; simpa only [validMask, ipnet.mask.ip_mask_to_prefix] using hn h
    · intro q h; exact hu q h
  | V6 a =>
    rcases IPv6MaskOps.candidate_spec a with ⟨p, _, hy, hn, hu⟩
    refine ⟨p, ?_, ?_, ?_⟩
    · intro h; simpa only [validMask, ipnet.mask.ip_mask_to_prefix] using hy h
    · intro h; simpa only [validMask, ipnet.mask.ip_mask_to_prefix] using hn h
    · intro q h; exact hu q h

theorem expectedNet_injective (ip : ipnet.core.net.ip_addr.IpAddr) (p q : U8)
    (h : expectedNet ip p = expectedNet ip q) : p = q := by
  cases ip with
  | V4 a =>
    have he := ipnet.ipnet.IpNet.V4.inj h
    exact congrArg ipnet.ipnet.Ipv4Net.prefix_len he
  | V6 a =>
    have he := ipnet.ipnet.IpNet.V6.inj h
    exact congrArg ipnet.ipnet.Ipv6Net.prefix_len he

/-- The actual tagged parser accepts exactly the independent contiguous-mask
    predicate, including zero, full and cross-family mask values. -/
theorem ip_mask_to_prefix_spec (m : ipnet.core.net.ip_addr.IpAddr) :
    ∃ out : core.result.Result U8 ipnet.ipnet.PrefixLenError,
      ipnet.mask.ip_mask_to_prefix m = Result.ok out ∧
      (∀ q : U8, out = .Ok q ↔ validMask m q.val) ∧
      (out = .Err () ↔ ¬∃ q : U8, validMask m q.val) := by
  rcases candidate m with ⟨p, hy, hn, hu⟩
  by_cases hv : validMask m p.val
  · refine ⟨.Ok p, hy hv, ?_, ?_⟩
    · intro q
      constructor
      · intro h; cases h; exact hv
      · intro h; exact congrArg core.result.Result.Ok (hu q h) |>.symm
    · constructor
      · intro h; cases h
      · intro h; exact False.elim (h ⟨p, hv⟩)
  · refine ⟨.Err (), hn hv, ?_, ?_⟩
    · intro q
      constructor
      · intro h; cases h
      · intro h; exact False.elim (hv ((hu q h) ▸ h))
    · constructor
      · intro _ ⟨q,hq⟩; exact hv ((hu q hq) ▸ hq)
      · intro _; rfl

private theorem with_netmask_ok (ip m : ipnet.core.net.ip_addr.IpAddr) (p : U8)
    (hm : ipnet.mask.ip_mask_to_prefix m = Result.ok (.Ok p)) :
    ipnet.ipnet.IpNet.with_netmask ip m =
      Result.ok (ipnet.ipnet.ipNewExpected ip p) := by
  rcases ipnet.ipnet.ip_new_spec ip p with ⟨out, ho, he⟩
  simp [ipnet.ipnet.IpNet.with_netmask, hm,
    core.result.Result.Insts.CoreOpsTry.branch, ho, he]

private theorem with_netmask_err (ip m : ipnet.core.net.ip_addr.IpAddr)
    (hm : ipnet.mask.ip_mask_to_prefix m = Result.ok (.Err ())) :
    ipnet.ipnet.IpNet.with_netmask ip m = Result.ok (.Err ()) := by
  simp [ipnet.ipnet.IpNet.with_netmask, hm,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Both tags are accepted according to the parsed mask prefix and the width
    of the address tag. The two tags need not match. -/
theorem with_netmask_spec (ip m : ipnet.core.net.ip_addr.IpAddr) :
    ∃ out : core.result.Result ipnet.ipnet.IpNet ipnet.ipnet.PrefixLenError,
      ipnet.ipnet.IpNet.with_netmask ip m = Result.ok out ∧
      (∀ q : U8,
        out = .Ok (expectedNet ip q) ↔
          validMask m q.val ∧ q.val ≤ addressWidth ip) ∧
      (out = .Err () ↔
        ¬∃ q : U8, validMask m q.val ∧ q.val ≤ addressWidth ip) := by
  rcases candidate m with ⟨p, hy, hn, hu⟩
  by_cases hv : validMask m p.val
  · have hcall := with_netmask_ok ip m p (hy hv)
    by_cases hw : p.val ≤ addressWidth ip
    · have hexp : ipnet.ipnet.ipNewExpected ip p = .Ok (expectedNet ip p) := by
        cases ip with
        | V4 a =>
          have hp : p.val ≤ 32 := by simpa [addressWidth] using hw
          simp [ipnet.ipnet.ipNewExpected, expectedNet, hp]
        | V6 a =>
          have hp : p.val ≤ 128 := by simpa [addressWidth] using hw
          simp [ipnet.ipnet.ipNewExpected, expectedNet, hp]
      refine ⟨.Ok (expectedNet ip p), by simpa [hexp] using hcall, ?_, ?_⟩
      · intro q
        constructor
        · intro h
          have hpq := expectedNet_injective ip p q
            (core.result.Result.Ok.inj h)
          subst q
          exact ⟨hv, hw⟩
        · rintro ⟨hq, _⟩
          have hqp := hu q hq
          subst q
          rfl
      · constructor
        · intro h; cases h
        · intro h; exact False.elim (h ⟨p, hv, hw⟩)
    · have hexp : ipnet.ipnet.ipNewExpected ip p = .Err () := by
        cases ip with
        | V4 a =>
          have hp : 32 < p.val := by
            have : ¬ p.val ≤ 32 := by simpa [addressWidth] using hw
            omega
          simp [ipnet.ipnet.ipNewExpected, hp]
        | V6 a =>
          have hp : 128 < p.val := by
            have : ¬ p.val ≤ 128 := by simpa [addressWidth] using hw
            omega
          simp [ipnet.ipnet.ipNewExpected, hp]
      refine ⟨.Err (), by simpa [hexp] using hcall, ?_, ?_⟩
      · intro q
        constructor
        · intro h; cases h
        · rintro ⟨hq, hwidth⟩
          have hqp := hu q hq
          subst q
          exact False.elim (hw hwidth)
      · constructor
        · intro _ ⟨q,hq,hwq⟩
          have hqp := hu q hq
          subst q
          exact hw hwq
        · intro _; rfl
  · refine ⟨.Err (), with_netmask_err ip m (hn hv), ?_, ?_⟩
    · intro q
      constructor
      · intro h; cases h
      · rintro ⟨hq, _⟩
        exact False.elim (hv ((hu q hq) ▸ hq))
    · constructor
      · intro _ ⟨q,hq,_⟩; exact hv ((hu q hq) ▸ hq)
      · intro _; rfl
end TaggedMask
