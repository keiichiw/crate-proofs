import Aeneas
open Aeneas Aeneas.Std
example : U32.shl 1#u32 32#u32 = Result.fail Error.integerOverflow := by rfl
example : U32.shr 1#u32 32#u32 = Result.fail Error.integerOverflow := by rfl
example : U128.shl 1#u128 128#u32 = Result.fail Error.integerOverflow := by rfl
example : U128.shr 1#u128 128#u32 = Result.fail Error.integerOverflow := by rfl
example : U32.shl 1#u32 31#u32 = Result.ok 2147483648#u32 := by rfl
example : U32.shr 2147483648#u32 31#u32 = Result.ok 1#u32 := by rfl
example : U128.shl 1#u128 127#u32 = Result.ok 170141183460469231731687303715884105728#u128 := by rfl
example : U128.shr 170141183460469231731687303715884105728#u128 127#u32 = Result.ok 1#u128 := by rfl
