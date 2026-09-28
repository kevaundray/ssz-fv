import SszArm.MeasureBitsListGateSteps

namespace SszArm.Measure.Bits.ListEntry

open Result

inductive Kind where | bounded | progressive deriving DecidableEq

def Kind.entry : Kind → Nat | .bounded => 1248 | .progressive => 684

def Kind.checked : Kind → Nat | .bounded => 1256 | .progressive => 692

def gateOps : Kind → List Op
  | .bounded => [p1248, p1252]
  | .progressive => [p684, p688]

@[irreducible] def gated (kind : Kind) (s : ArmState) (base : BitVec 64) : ArmState :=
  let flags := (AddWithCarry ((r (.GPR 8#5) s).setWidth 32) (~~~3#32) 1#1).2
  w .PC (if flags.z = 1#1 then base + BitVec.ofNat 64 kind.checked else base + 3924#64)
    (write_pstate flags s)

theorem gate_run (kind : Kind) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.entry) :
    run 2 s = gated kind s base := by
  let flags := (AddWithCarry ((r (.GPR 8#5) s).setWidth 32) (~~~3#32) 1#1).2
  cases kind with
  | bounded =>
    have first : stepi s = listGateStage s (base + 1252#64) flags :=
      (Op.step p1248 s base code error pc).trans (listGateStage_bounded_compare s base pc)
    have second : stepi (listGateStage s (base + 1252#64) flags) = gated .bounded s base := by
      calc
        _ = p1252.effect (listGateStage s (base + 1252#64) flags) :=
          Op.step p1252 _ base (code.congr (listGateStage_program s _ flags))
            ((listGateStage_error s _ flags).trans error) (listGateStage_pc s _ flags)
        _ = w .PC (if flags.z = 1#1 then base + 1256#64 else base + 3924#64)
            (write_pstate flags s) := listGateStage_bounded_branch s base flags
        _ = gated .bounded s base := by
          unfold gated
          rfl
    exact list_gate_two_steps s _ _ first second
  | progressive =>
    have first : stepi s = listGateStage s (base + 688#64) flags :=
      (Op.step p684 s base code error pc).trans (listGateStage_progressive_compare s base pc)
    have second : stepi (listGateStage s (base + 688#64) flags) = gated .progressive s base := by
      calc
        _ = p688.effect (listGateStage s (base + 688#64) flags) :=
          Op.step p688 _ base (code.congr (listGateStage_program s _ flags))
            ((listGateStage_error s _ flags).trans error) (listGateStage_pc s _ flags)
        _ = w .PC (if flags.z = 1#1 then base + 692#64 else base + 3924#64)
            (write_pstate flags s) := listGateStage_progressive_branch s base flags
        _ = gated .progressive s base := by
          unfold gated
          rfl
    exact list_gate_two_steps s _ _ first second

@[simp] theorem gated_program (kind : Kind) (s : ArmState) (base : BitVec 64) :
    (gated kind s base).program = s.program := by simp [gated, state_simp_rules]
@[simp] theorem gated_error (kind : Kind) (s : ArmState) (base : BitVec 64) :
    read_err (gated kind s base) = read_err s := by simp [gated, state_simp_rules]
@[simp] theorem gated_register (kind : Kind) (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (gated kind s base) = r (.GPR reg) s := by simp [gated, state_simp_rules]
@[simp] theorem gated_vector (kind : Kind) (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (gated kind s base) = r (.SFP reg) s := by simp [gated, state_simp_rules]
@[simp] theorem gated_memory (kind : Kind) (s : ArmState) (base : BitVec 64) :
    (gated kind s base).mem = s.mem := by simp [gated, state_simp_rules]

theorem gated_pc_bits (kind : Kind) (s : ArmState) (base : BitVec 64)
    (tag : (r (.GPR 8#5) s).setWidth 32 = 3#32) :
    read_pc (gated kind s base) = base + BitVec.ofNat 64 kind.checked := by
  simp [gated, tag, state_simp_rules, AddWithCarry]

theorem gated_pc_wrong (kind : Kind) (s : ArmState) (base : BitVec 64)
    (value : SszNative.Serialize.Value)
    (tag : r (.GPR 8#5) s = (Emit.valueTag value).setWidth 64)
    (notBits : ∀ bits, value ≠ .bits bits) :
    read_pc (gated kind s base) = base + 3924#64 := by
  cases value with
  | bits bits => exact False.elim (notBits bits rfl)
  | bool flag | uint flag | bytes flag | seq flag =>
    simp [gated, tag, Emit.valueTag, state_simp_rules, AddWithCarry]
  | union selector content =>
    simp [gated, tag, Emit.valueTag, state_simp_rules, AddWithCarry]

end SszArm.Measure.Bits.ListEntry
