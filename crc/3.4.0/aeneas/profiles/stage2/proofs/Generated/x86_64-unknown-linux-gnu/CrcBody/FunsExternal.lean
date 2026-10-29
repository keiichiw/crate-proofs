module
public import CrcBody.Types
public import CrcStage2.Funs
@[expose] public section
namespace CrcBody
/- These standard-library boundary definitions reuse the separately source-extracted
   Rust reverse_bits wrappers. Their only primitive boundary is the explicitly
   reviewed five-scalar bitreverse model in CrcStage2.FunsExternal. -/
noncomputable def core.num.U8.reverse_bits := CrcStage2.core.num.U8.reverse_bits
noncomputable def core.num.U16.reverse_bits := CrcStage2.core.num.U16.reverse_bits
noncomputable def core.num.U32.reverse_bits := CrcStage2.core.num.U32.reverse_bits
noncomputable def core.num.U64.reverse_bits := CrcStage2.core.num.U64.reverse_bits
noncomputable def core.num.U128.reverse_bits := CrcStage2.core.num.U128.reverse_bits
end CrcBody
