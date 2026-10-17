module
public import Ipnet

public section
open Aeneas Aeneas.Std Result
namespace PrefixLenErrorValue

/-- The derived Clone implementation preserves the unique error value. -/
theorem clone_spec (e : ipnet.ipnet.PrefixLenError) :
    ipnet.ipnet.PrefixLenError.Insts.CoreCloneClone.clone e = Result.ok e := by
  cases e
  rfl

/-- The derived PartialEq body returns true for the singleton error type. -/
theorem eq_spec (a b : ipnet.ipnet.PrefixLenError) :
    ipnet.ipnet.PrefixLenError.Insts.CoreCmpPartialEqPrefixLenError.eq a b =
      Result.ok true := by
  cases a
  cases b
  rfl

end PrefixLenErrorValue
