import CrcProofs.Util
import CrcProofs.Wide
open Aeneas Aeneas.Std Aeneas.Std.WP
namespace crc

theorem step8_polynomial (poly value : U8) (reflect : Bool) :
    (step8 poly value reflect).bv = polynomialStep poly.bv value.bv reflect := by
  cases reflect with
  | true => exact congrArg (fun a : BitVec 8 => (value.bv >>> 1) ^^^ a) (lowBit_mul value.bv poly.bv)
  | false =>
    have h := lowBit_mul (value.bv >>> 7) poly.bv
    have heq : (value.bv >>> 7).getLsbD 0 = value.bv.getLsbD 7 := by simp
    have h' : ((value.bv >>> 7) &&& (1 : BitVec 8)) * poly.bv =
        if value.bv.getLsbD 7 then poly.bv else 0 := h.trans (by rw [heq])
    exact congrArg (fun a : BitVec 8 => (value.bv <<< 1) ^^^ a) h'

theorem run8_polynomial (poly value : U8) (reflect : Bool) (k : Nat) :
    (run8 poly reflect k value).bv = polynomialRun poly.bv reflect k value.bv := by
  induction k generalizing value with
  | zero => rfl
  | succ k ih =>
    simp only [run8, polynomialRun]
    exact (ih (step8 poly value reflect)).trans
      (congrArg (polynomialRun poly.bv reflect k) (step8_polynomial poly value reflect))

theorem crc8_polynomial_spec (poly value : U8) (reflect : Bool) :
    ∃ out, util.crc8 poly reflect value = .ok out ∧
      out.bv = polynomialRun poly.bv reflect 8 value.bv := by
  obtain ⟨out, hout, hv⟩ := crc8_total_spec poly value reflect
  exact ⟨out, hout, (congrArg UScalar.bv hv).trans (run8_polynomial poly value reflect 8)⟩
end crc
