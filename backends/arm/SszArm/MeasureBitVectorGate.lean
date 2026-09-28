import SszArm.MeasureBitVectorGateComposition

namespace SszArm.Measure.BitVector

open Result

def gateOps : List Op := [p568, p572]

@[irreducible] def gated (s : ArmState) (base : BitVec 64) : ArmState :=
  let flags := (AddWithCarry ((r (.GPR 8#5) s).setWidth 32) (~~~3#32) 1#1).2
  w .PC (if flags.z = 1#1 then base + 576#64 else base + 3924#64) (write_pstate flags s)

theorem gate_run (s : ArmState) (base : BitVec 64) (code : CodeAt s base)
    (error : read_err s = .None) (pc : read_pc s = base + 568#64) :
    run 2 s = gated s base := by
  let flags := (AddWithCarry ((r (.GPR 8#5) s).setWidth 32) (~~~3#32) 1#1).2
  have first : stepi s = gateStage s base flags :=
    (Op.step p568 s base code error pc).trans (gateStage_compare s base pc)
  have second : stepi (gateStage s base flags) = gated s base := by
    calc
      _ = p572.effect (gateStage s base flags) :=
        Op.step p572 _ base (code.congr (gateStage_program s base flags))
          ((gateStage_error s base flags).trans error) (gateStage_pc s base flags)
      _ = w .PC (if flags.z = 1#1 then base + 576#64 else base + 3924#64)
          (write_pstate flags s) := gateStage_branch s base flags
      _ = gated s base := by
        unfold gated
        rfl
  change stepi (stepi s) = gated s base
  rw [first]
  exact second

@[simp] theorem gated_program (s : ArmState) (base : BitVec 64) :
    (gated s base).program = s.program := by simp [gated, state_simp_rules]

@[simp] theorem gated_error (s : ArmState) (base : BitVec 64) :
    read_err (gated s base) = read_err s := by simp [gated, state_simp_rules]

@[simp] theorem gated_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (gated s base) = r (.GPR reg) s := by simp [gated, state_simp_rules]

@[simp] theorem gated_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (gated s base) = r (.SFP reg) s := by simp [gated, state_simp_rules]

@[simp] theorem gated_memory (s : ArmState) (base : BitVec 64) :
    (gated s base).mem = s.mem := by simp [gated, state_simp_rules]

theorem gated_pc_bits (s : ArmState) (base : BitVec 64)
    (tag : (r (.GPR 8#5) s).setWidth 32 = 3#32) :
    read_pc (gated s base) = base + 576#64 := by
  simp [gated, tag, state_simp_rules, AddWithCarry]

theorem gated_pc_wrong (s : ArmState) (base : BitVec 64) (value : SszNative.Serialize.Value)
    (tag : r (.GPR 8#5) s = (Emit.valueTag value).setWidth 64)
    (notBits : ∀ bits, value ≠ .bits bits) : read_pc (gated s base) = base + 3924#64 := by
  cases value with
  | bits bits => exact False.elim (notBits bits rfl)
  | bool flag | uint flag | bytes flag | seq flag =>
    simp [gated, tag, Emit.valueTag, state_simp_rules, AddWithCarry]
  | union selector content => simp [gated, tag, Emit.valueTag, state_simp_rules, AddWithCarry]

end SszArm.Measure.BitVector
