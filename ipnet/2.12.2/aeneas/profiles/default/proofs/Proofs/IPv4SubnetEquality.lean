module
public import Proofs.IPv4AddressEq
public import Proofs.IPv4SubnetStep

public section
open Aeneas Aeneas.Std Result
namespace IPv4SubnetStep
/-- The extracted IPv4 equality body returns the structural equality test. -/
theorem ipv4_eq_bool (a b : ipnet.core.net.ip_addr.Ipv4Addr) :
  ∃ out, ipnet.core.net.ip_addr.Ipv4Addr.Insts.CoreCmpPartialEqIpv4Addr.eq a b =
    Result.ok out ∧ (out ↔ a = b) := by
  have hmodel :
      core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a.octets b.octets =
        core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8
          a.octets.to_slice b.octets.to_slice := by
    simp [core.array.equality.PartialEqArray.eq,
      core.slice.cmp.PartialEqSlice.eq, Array.to_slice]
  have hne (x y : U8) :
      core.cmp.PartialEqU8.ne x y ⦃ z => z ↔ x ≠ y ⦄ := by
    simp [core.cmp.impls.PartialEqU8.ne]
  have hs := core.slice.cmp.PartialEqSlice.eq_homo_spec
    core.cmp.PartialEqU8 a.octets.to_slice b.octets.to_slice hne
  have hs' :
      core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a.octets b.octets
        ⦃ z => z ↔ a = b ⦄ := by
    rw [hmodel]
    apply WP.spec_mono hs
    intro z hz
    have heq : a.octets.to_slice = b.octets.to_slice ↔ a = b := by
      constructor
      · intro h
        have hval : a.octets.val = b.octets.val := by
          simpa [Slice.eq_iff, Array.to_slice] using h
        have harr : a.octets = b.octets := (Array.eq_iff _ _).mpr hval
        cases a; cases b; cases harr; rfl
      · intro h
        subst b
        rfl
    simpa only [heq] using hz
  have hs'' :
      ipnet.core.net.ip_addr.Ipv4Addr.Insts.CoreCmpPartialEqIpv4Addr.eq a b
        ⦃ z => z ↔ a = b ⦄ := by
    simpa only [ipnet.core.net.ip_addr.Ipv4Addr.Insts.CoreCmpPartialEqIpv4Addr.eq]
      using hs'
  cases hresult :
      ipnet.core.net.ip_addr.Ipv4Addr.Insts.CoreCmpPartialEqIpv4Addr.eq a b with
  | ret z =>
      refine ⟨z, rfl, ?_⟩
      simpa [hresult] using hs''
  | vis _ _ => simp [hresult] at hs''
  | div => simp [hresult] at hs''
/-- Equality in the extracted body agrees with the independent big-endian value. -/
theorem ipv4_eq_value (a b : ipnet.core.net.ip_addr.Ipv4Addr) :
    ∃ out, ipnet.core.net.ip_addr.Ipv4Addr.Insts.CoreCmpPartialEqIpv4Addr.eq a b =
      Result.ok out ∧
      (out ↔ CidrModel.ipv4Value a = CidrModel.ipv4Value b) := by
  rcases ipv4_eq_bool a b with ⟨out,hr,hiff⟩
  exact ⟨out,hr,hiff.trans (IPv4AddressEq.ipv4Value_eq_iff a b).symm⟩

end IPv4SubnetStep
