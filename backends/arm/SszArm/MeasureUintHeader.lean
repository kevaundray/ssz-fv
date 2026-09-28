import SszArm.MeasureUintWidthSelect

namespace SszArm.Measure.Uint

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value)

def widthHeader (s : ArmState) (base : BitVec 64) : ArmState := WidthOp.p2736.effect base s

theorem width_header_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 2736#64) : run 1 s = widthHeader s base := by
  change stepi s = WidthOp.p2736.effect base s
  exact width_step s base .p2736 code pc error aligned

@[simp] theorem width_header_program (s : ArmState) (base : BitVec 64) :
    (widthHeader s base).program = s.program := WidthOp.program _ _ _

@[simp] theorem width_header_error (s : ArmState) (base : BitVec 64) :
    read_err (widthHeader s base) = read_err s := WidthOp.error _ _ _

@[simp] theorem width_header_memory (s : ArmState) (base : BitVec 64) :
    (widthHeader s base).mem = s.mem := by
  simp [widthHeader, WidthOp.effect, put, next, Emit.Dispatch.next, state_simp_rules]

theorem width_header_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (twenty : reg ≠ 20#5) (twentyOne : reg ≠ 21#5) :
    r (.GPR reg) (widthHeader s base) = r (.GPR reg) s := by
  simp [widthHeader, WidthOp.effect, put, next, Emit.Dispatch.next,
    state_simp_rules, twenty, twentyOne]

@[simp] theorem width_header_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (widthHeader s base) = r (.SFP reg) s := WidthOp.vector _ _ _ _

@[simp] theorem width_header_outcome (s : ArmState) (base : BitVec 64) (args : Args)
    (desc : Desc) (value : Value) :
    outcome (widthHeader s base) args desc value = outcome s args desc value := by
  simp [widthHeader, WidthOp.effect, put, next, Emit.Dispatch.next,
    outcome, arenaOf, state_simp_rules]

theorem width_header_owned {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (base : BitVec 64) :
    Owned (widthHeader s base) args desc value := by
  apply owned.of_local_frame
  intro address outside
  simp

theorem width_header_pair {s : ArmState} {args : Args} {uintCap number : NatOperand}
    (owned : Owned s args (.uint uintCap) (.uint number)) (base : BitVec 64)
    (descriptor : r (.GPR 1#5) s = args.descriptor) :
    r (.GPR 21#5) (widthHeader s base) = uintCap.pointer ∧
      r (.GPR 20#5) (widthHeader s base) = uintCap.payload := by
  have pair := descriptor_pair owned
  simpa [widthHeader, WidthOp.effect, put, next, Emit.Dispatch.next,
    state_simp_rules, descriptor] using pair

theorem produced_prepend_header {s t : ArmState} {args : Args} {desc : Desc} {value : Value}
    {base : BitVec 64} (after : Produced (widthHeader s base) t args desc value base) :
    Produced s t args desc value base := by
  refine { after with
    program := after.program.trans (width_header_program s base)
    result := ?_
    cursor := ?_
    header := ?_
    written := ?_
    frame := ?_
    registers := ?_
    vectors := ?_ }
  · simpa only [width_header_outcome] using after.result
  · simpa only [width_header_outcome] using after.cursor
  · simpa [widthHeader, WidthOp.effect, put, next, Emit.Dispatch.next,
      state_simp_rules] using after.header
  · simpa only [width_header_outcome] using after.written
  · intro address outside
    have preserved := after.frame address (by simpa only [width_header_outcome] using outside)
    simpa only [width_header_memory] using preserved
  · intro reg member
    have twenty : reg ≠ 20#5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    have twentyOne : reg ≠ 21#5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    exact (after.registers reg member).trans (width_header_register s base reg twenty twentyOne)
  · intro reg low high
    rw [after.vectors reg low high, width_header_vector]

end SszArm.Measure.Uint
