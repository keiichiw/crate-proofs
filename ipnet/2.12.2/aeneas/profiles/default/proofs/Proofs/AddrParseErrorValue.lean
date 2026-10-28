module
public import Ipnet

public section
open Aeneas Aeneas.Std Result
namespace AddrParseErrorValue

/-- Clone preserves the unique exported parse-error value. -/
theorem clone_spec (e : ipnet.parser.AddrParseError) :
    ipnet.parser.AddrParseError.Insts.CoreCloneClone.clone e = Result.ok e := by
  cases e
  simp [ipnet.parser.AddrParseError.Insts.CoreCloneClone.clone,
    Aeneas.Std.builtinClone_unit_spec]

/-- PartialEq of the singleton parse-error type always returns true. -/
theorem eq_spec (a b : ipnet.parser.AddrParseError) :
    ipnet.parser.AddrParseError.Insts.CoreCmpPartialEqAddrParseError.eq a b =
      Result.ok true := by
  cases a
  cases b
  simp [ipnet.parser.AddrParseError.Insts.CoreCmpPartialEqAddrParseError.eq,
    core.cmp.impls.PartialEqUnit.eq]

end AddrParseErrorValue
