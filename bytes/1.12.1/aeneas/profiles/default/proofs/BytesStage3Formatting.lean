module
public import Aeneas.Std.Core.Fmt
public section
namespace Aeneas.Std
/-- The existing formatting abstraction already discards both arguments. -/
@[expose]
def core.fmt.rt.Argument.new_debug_without_dictionary {T : Type _}
    (_ : T) : Result core.fmt.rt.Argument := .ok ()
theorem core.fmt.rt.Argument.new_debug_dictionary_erasure {T : Type _}
    (inst : core.fmt.Debug T) (x : T) :
    core.fmt.rt.Argument.new_debug inst x =
      core.fmt.rt.Argument.new_debug_without_dictionary x := rfl
end Aeneas.Std
