import Stage2Proofs.WidthEndpoints
import Stage2Proofs.FullWidthSpec
namespace CrcPartialSpec

/-- Storage representation of a bounded canonical register. Input reflection reverses
    its MSB-aligned physical word; this is an encoding, not a different CRC degree. -/
abbrev physical := @CrcWidthEndpoints.storedEncode

/-- Canonical byte transition in the independently specified width-w register. -/
def byteStep {w : Nat} (refin : Bool) (poly state : BitVec w) (byte : BitVec 8) : BitVec w :=
  if refin then CrcReflectedWide.byteStep poly state byte
  else CrcCanonicalWide.byteStep poly state byte

/-- A coherent physical table stores encoded single-byte transitions from zero. -/
def tableEntry {w : Nat} (N : Nat) (refin : Bool) (poly : BitVec w) (byte : BitVec 8) : BitVec N :=
  physical N refin (byteStep refin poly 0 byte)

abbrev run := @CrcFullWidthSpec.run
abbrev checksum := @CrcFullWidthSpec.checksum

end CrcPartialSpec
