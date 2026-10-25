module
public import Aeneas.Std.Slice
public import Aeneas.Std.Core.Result
public section
namespace Aeneas.Std
/-- Exact two-field representation of the original public error; no invariant. -/
structure BytesTryGetError where
  requested : Usize
  available : Usize
/-- Interface projection only. Every operational field is supplied by actual
extracted implementations; this record states no behavioral law. -/
structure BytesBufExtended (Self : Type _) where
  remaining : Self → Result Usize
  chunk : Self → Result (Slice U8)
  advance : Self → Usize → Result Self
  has_remaining : Self → Result Bool
  try_copy_to_slice : Self → Slice U8 → Result (core.result.Result Unit BytesTryGetError × Self × Slice U8)
end Aeneas.Std
