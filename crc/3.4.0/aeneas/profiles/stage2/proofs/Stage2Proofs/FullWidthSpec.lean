import Stage2Proofs.ByteMathWide
import Stage2Proofs.ReflectMathWide
namespace CrcFullWidthSpec
/-- Full-width canonical register: input reflection changes only the order of byte bits. -/
def run {N : Nat} (refin : Bool) (poly initial : BitVec N)
    (bytes : List (BitVec 8)) : BitVec N :=
  if refin then CrcReflectedWide.run poly initial bytes
  else CrcCanonicalWide.run poly initial bytes

def decode {N : Nat} (refin : Bool) (storage : BitVec N) : BitVec N :=
  if refin then storage.reverse else storage

def finish {N : Nat} (refout : Bool) (xorout state : BitVec N) : BitVec N :=
  (if refout then state.reverse else state) ^^^ xorout

def checksum {N : Nat} (refin refout : Bool) (poly initial xorout : BitVec N)
    (bytes : List (BitVec 8)) : BitVec N :=
  finish refout xorout (run refin poly initial bytes)
end CrcFullWidthSpec
