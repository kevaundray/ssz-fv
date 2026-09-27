import Arm.Exec

namespace SszArm.LogicalImmediateRegression

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Decode the actual instruction word before executing the model semantics. -/
def executeWord (word : BitVec 32) (s : ArmState) : Option ArmState :=
  (decode_raw_inst word).map (fun instruction => exec_inst instruction s)

/-- The actual SSZ MOV/ORR word ignores every possible incoming SP value.
The whole-state equality also retains the incoming flags, SP, memory, program,
error field and all non-destination registers; no SP precondition is needed. -/
theorem actual_mov_arbitrary_state (s : ArmState) :
    executeWord 0xb27fefe9#32 s =
      some (write_gpr 64 9#5 0x1ffffffffffffffe#64
        (write_pc (read_pc s + 4#64) s)) := by
  change some (DPI.exec_logical_imm
    { sf := 1#1, opc := 1#2, N := 1#1, immr := 63#6, imms := 59#6,
      Rn := 31#5, Rd := 9#5 } s) = _
  simp (config := {decide := true, instances := true})
    [state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]

/-- Correcting the source must not change the non-flag-setting destination:
Rd31 still writes SP, while Rn31 reads zero and NZCV remains unchanged. -/
theorem orr_destination_sp (s : ArmState) :
    executeWord 0xb27fefff#32 s =
      some (write_gpr 64 31#5 0x1ffffffffffffffe#64
        (write_pc (read_pc s + 4#64) s)) := by
  change some (DPI.exec_logical_imm
    { sf := 1#1, opc := 1#2, N := 1#1, immr := 63#6, imms := 59#6,
      Rn := 31#5, Rd := 31#5 } s) = _
  simp (config := {decide := true, instances := true})
    [state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq]

/-- ANDS uses ZR for Rd31, retaining arbitrary SP and every GPR, but replaces
all four flags with the architectural flags of the zero result: NZCV=0100. -/
theorem ands_destination_zr_flags (s : ArmState) :
    executeWord 0xf27fefff#32 s =
      some (write_pstate (make_pstate 0#1 1#1 0#1 0#1)
        (write_pc (read_pc s + 4#64) s)) := by
  change some (DPI.exec_logical_imm
    { sf := 1#1, opc := 3#2, N := 1#1, immr := 63#6, imms := 59#6,
      Rn := 31#5, Rd := 31#5 } s) = _
  simp (config := {decide := true, instances := true})
    [DPI.update_logical_imm_pstate, state_simp_rules, bitvec_rules,
      minimal_theory, zero_flag_spec]

end SszArm.LogicalImmediateRegression
