module
public import Proofs.IPv4SubnetEquality
public import Proofs.Comparisons

public section

/-! Actual derived value-trait bodies for `Ipv4Net`. These compare the stored
address and prefix fields, not CIDR address sets. -/
namespace IPv4Derived

open Aeneas Aeneas.Std Result

@[expose] def key (n : ipnet.ipnet.Ipv4Net) : Nat × Nat :=
  (CidrModel.ipv4Value n.addr, n.prefix_len.val)

@[expose] def keyCompare (a b : ipnet.ipnet.Ipv4Net) : Ordering :=
  match compare (key a).1 (key b).1 with
  | .lt => .lt
  | .eq => compare (key a).2 (key b).2
  | .gt => .gt

theorem clone_spec (n : ipnet.ipnet.Ipv4Net) :
    ipnet.ipnet.Ipv4Net.Insts.CoreCloneClone.clone n = Result.ok n := by
  rfl

theorem eq_spec (a b : ipnet.ipnet.Ipv4Net) :
    ∃ out, ipnet.ipnet.Ipv4Net.Insts.CoreCmpPartialEqIpv4Net.eq a b =
      Result.ok out ∧ (out ↔ key a = key b) := by
  rcases IPv4SubnetStep.ipv4_eq_value a.addr b.addr with ⟨out, hout, hiff⟩
  by_cases hp : a.prefix_len = b.prefix_len
  · refine ⟨out, ?_, ?_⟩
    · simp [ipnet.ipnet.Ipv4Net.Insts.CoreCmpPartialEqIpv4Net.eq, hp, hout]
    · simp [key, hp, hiff]
  · refine ⟨false, ?_, ?_⟩
    · simp [ipnet.ipnet.Ipv4Net.Insts.CoreCmpPartialEqIpv4Net.eq, hp]
    · have hpval : a.prefix_len.val ≠ b.prefix_len.val := by
        intro h
        exact hp (UScalar.eq_of_val_eq h)
      simp [key, hpval]

theorem cmp_spec (a b : ipnet.ipnet.Ipv4Net) :
    ipnet.ipnet.Ipv4Net.Insts.CoreCmpOrd.cmp a b =
      Result.ok (keyCompare a b) := by
  simp [ipnet.ipnet.Ipv4Net.Insts.CoreCmpOrd.cmp,
    Comparisons.ipv4_cmp_spec, keyCompare, key,
    core.cmp.impls.OrdU8.cmp, bind_ok]
  cases h : compare (CidrModel.ipv4Value a.addr)
      (CidrModel.ipv4Value b.addr) <;> simp

theorem partial_cmp_spec (a b : ipnet.ipnet.Ipv4Net) :
    ipnet.ipnet.Ipv4Net.Insts.CoreCmpPartialOrdIpv4Net.partial_cmp a b =
      Result.ok (some (keyCompare a b)) := by
  simp [ipnet.ipnet.Ipv4Net.Insts.CoreCmpPartialOrdIpv4Net.partial_cmp,
    cmp_spec, bind_ok]

end IPv4Derived
