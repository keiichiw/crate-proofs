module
public import Adler2

public section

open Aeneas.Std

namespace adler2

/-- Bootstrap contract for the actual extracted public constructor. -/
theorem new_spec :
    Adler32.new = Result.ok { a := 1#u16, b := 0#u16 } := by
  rfl

/-- Kernel-checked evaluation of the initial state's checksum. -/
theorem initial_checksum :
    Adler32.checksum { a := 1#u16, b := 0#u16 } = Result.ok 1#u32 := by
  simp only [Adler32.checksum, lift, bind_ok]
  have shift : (core.convert.num.FromU32U16.from 0#u16 <<< 16#i32) = Result.ok 0#u32 := by rfl
  rw [shift]
  simp only [bind_ok]
  rfl

end adler2
