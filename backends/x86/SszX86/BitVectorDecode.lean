import SszX86.BitVectorCore

namespace SszX86.BitVector
open Kraken.X64.Parser

theorem program_length : program.length = 228 := by rfl

/-- Decode only the selected concrete instruction. Membership is checked against
all pinned rows, without simplifying the complete parsed table into the goal. -/
macro "bitvector_decoded_step " row:num " at " pc:num " size " bytes:num " code " instructions:term
    " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have member := List.getElem_mem (l := SszX86.BitVector.program) (n := $row)
     (by rw [SszX86.BitVector.program_length]; decide)
   have fetched := SszX86.BitVector.step_at _ _ $hc
     (($pc, $bytes, $instructions) : Nat × Nat × Program) member
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.BitVector.directives, SszX86.BitVector.labels, Directives.interp, Directive.interp,
      Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp, Reg.interp,
      AddrExpr.interp, ConstExpr.interp, RelRegOrMem.interp, BitVec.toAddressSize,
      MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop,
      BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      Int64.add_assoc, Width.bytes, Width.bits]))

end SszX86.BitVector
