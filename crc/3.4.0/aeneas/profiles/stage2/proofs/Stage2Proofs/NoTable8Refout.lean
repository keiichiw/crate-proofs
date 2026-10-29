import Stage2Proofs.NoTable8
import Stage2Proofs.Refout8
open Aeneas Aeneas.Std Result
namespace CrcNoTable8

/-- Full-width, non-reflected input CRC with arbitrary output reflection; no stored table invariant. -/
theorem checksum_nonref (self : Crc8) (bytes : Slice U8)
    (ha : CrcRefout8.NonRef8 self.algorithm) :
    ∃ out, CrcBody.crc8.CrcU8Table.checksum self bytes = .ok out ∧
      out.bv = (if self.algorithm.refout then
        (CrcCanonical8.run self.algorithm.poly.bv self.algorithm.init.bv
          (bytes.val.map UScalar.bv)).reverse else
        CrcCanonical8.run self.algorithm.poly.bv self.algorithm.init.bv
          (bytes.val.map UScalar.bv)) ^^^ self.algorithm.xorout.bv := by
  obtain ⟨mid, hm, hv⟩ := update8_canonical self self.algorithm.init bytes ha.1 ha.2
  obtain ⟨out, hout, hfin⟩ := CrcRefout8.finalize_total self.algorithm mid ha
  refine ⟨out, ?_, ?_⟩
  · simp only [CrcBody.crc8.CrcU8Table.checksum, CrcRefout8.init_identity _ _ ha,
      hm, hout, bind_ok]
  · simpa only [hv] using hfin

end CrcNoTable8
