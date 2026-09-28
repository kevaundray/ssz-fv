import SszX86.MeasurePost

namespace SszX86.Measure
open SszNative SszNative.Serialize UintCodec

theorem ResultAt.success_owned (observe : Nat → Nat → Option Nat) (out : Nat)
    (operand : NatOperand) (stored : ResultAt observe out (.ok operand)) :
    NatArithmetic.operandAt observe (out + 16) operand := stored.2.2.1

theorem ResultAt.scope_owned (observe : Nat → Nat → Option Nat) (out : Nat)
    (expected actual : NatOperand) (stored : ResultAt observe out (.error (.scope expected actual))) :
    NatArithmetic.operandAt observe (out + 16) expected ∧
      NatArithmetic.operandAt observe (out + 32) actual :=
  ⟨stored.2.2.1, stored.2.2.2.1⟩

theorem ResultAt.limit_owned (observe : Nat → Nat → Option Nat) (out : Nat)
    (expected actual : NatOperand) (stored : ResultAt observe out (.error (.limit expected actual))) :
    NatArithmetic.operandAt observe (out + 16) expected ∧
      NatArithmetic.operandAt observe (out + 32) actual :=
  ⟨stored.2.2.1, stored.2.2.2.1⟩

/-- The public observation retains represented size ownership, not only a Nat
value. This is the operand a subsequent encoded-size/emit wrapper consumes. -/
theorem Post.success_owned {s : MachineData} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64} {t : MachineState}
    (post : Post s desc value buffer address capacity used ra t)
    (operand : NatOperand)
    (success : (measure desc value (arenaState address capacity used)).result = .ok operand) :
    NatArithmetic.operandAt (widthLoad t.1.dmem) (s.regs.rdi.toNat + 16) operand := by
  have stored := post.observed
  rw [success] at stored
  exact stored.success_owned

theorem Post.scope_owned {s : MachineData} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64} {t : MachineState}
    (post : Post s desc value buffer address capacity used ra t)
    (expected actual : NatOperand)
    (failure : (measure desc value (arenaState address capacity used)).result =
      .error (.scope expected actual)) :
    NatArithmetic.operandAt (widthLoad t.1.dmem) (s.regs.rdi.toNat + 16) expected ∧
      NatArithmetic.operandAt (widthLoad t.1.dmem) (s.regs.rdi.toNat + 32) actual := by
  have stored := post.observed
  rw [failure] at stored
  exact stored.scope_owned

theorem Post.limit_owned {s : MachineData} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64} {t : MachineState}
    (post : Post s desc value buffer address capacity used ra t)
    (expected actual : NatOperand)
    (failure : (measure desc value (arenaState address capacity used)).result =
      .error (.limit expected actual)) :
    NatArithmetic.operandAt (widthLoad t.1.dmem) (s.regs.rdi.toNat + 16) expected ∧
      NatArithmetic.operandAt (widthLoad t.1.dmem) (s.regs.rdi.toNat + 32) actual := by
  have stored := post.observed
  rw [failure] at stored
  exact stored.limit_owned

/-- The already checked logical measure refinement targets the pinned SSZ result,
including semantic errors and exact ScratchExhausted precedence. -/
theorem outcome_refines_pinned (desc : Desc) (value : Value) (arena : Delimited.ArenaState)
    (physical : value.Physical) :
    Measures (measure desc value arena).result
      ((Ssz.serialize desc.erase value.erase).map Array.size) := by
  rw [← expectedSize_eq_pinned desc value]
  exact measure_refines desc value arena physical

end SszX86.Measure
