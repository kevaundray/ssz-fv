import SszArm.SerializeEntry

namespace SszArm.Serialize

private def emitCallOps : List Op := [.p648, .p652, .p656, .p660, .p664, .p668]

@[irreducible] def emitterEntry (base : BitVec 64) (s : ArmState) : ArmState :=
  block base emitCallOps s

@[simp] theorem emitterEntry_program (base : BitVec 64) (s : ArmState) :
    (emitterEntry base s).program = s.program := by
  simp [emitterEntry]

@[simp] theorem emitterEntry_error (base : BitVec 64) (s : ArmState) :
    read_err (emitterEntry base s) = read_err s := by
  simp [emitterEntry]

@[simp] theorem emitterEntry_memory (base : BitVec 64) (s : ArmState) :
    (emitterEntry base s).mem = s.mem := by
  simp [emitterEntry, emitCallOps, block, Op.effect, put, next, state_simp_rules]

@[simp] theorem emitterEntry_pc (base : BitVec 64) (s : ArmState) :
    read_pc (emitterEntry base s) = base + emitOffset := by
  simp [emitterEntry, emitCallOps, block, Op.effect, put, next, state_simp_rules]

@[simp] theorem emitterEntry_lr (base : BitVec 64) (s : ArmState) :
    r (.GPR 30#5) (emitterEntry base s) = base + 672#64 := by
  simp [emitterEntry, emitCallOps, block, Op.effect, put, next, state_simp_rules]

theorem emitterEntry_register (base : BitVec 64) (s : ArmState) (reg : BitVec 5)
    (outside : reg ∉ [0#5, 1#5, 2#5, 3#5, 4#5, 30#5]) :
    r (.GPR reg) (emitterEntry base s) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  simp [emitterEntry, emitCallOps, block, Op.effect, put, next, state_simp_rules,
    outside.1, outside.2.1, outside.2.2.1, outside.2.2.2.1,
    outside.2.2.2.2.1, outside.2.2.2.2.2]

@[simp] theorem emitterEntry_vector (base : BitVec 64) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (emitterEntry base s) = r (.SFP reg) s := by
  simp [emitterEntry]

theorem emitterEntry_aligned (base : BitVec 64) (s : ArmState)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (emitterEntry base s) := by
  simpa only [emitterEntry] using block_aligned base emitCallOps s aligned

theorem emitterEntry_args (base : BitVec 64) (s : ArmState) (args : Args) (count : Nat)
    (registers : Registers s args) (payload : r (.GPR 5#5) s = BitVec.ofNat 64 count) :
    Emit.Args.ofEntry (emitterEntry base s) = args.emit count := by
  rcases registers with ⟨result, output, value, descriptor, capacity, stack⟩
  simp [emitterEntry, emitCallOps, block, Op.effect, put, next, state_simp_rules,
    Emit.Args.ofEntry, Args.emit, result, output, value, descriptor, stack, payload]

theorem emitterEntry_registers (base : BitVec 64) (s : ArmState) (args : Args)
    (registers : Registers s args) : Registers (emitterEntry base s) args := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [emitterEntry_register base s 19#5 (by decide)]; exact registers.result
  · rw [emitterEntry_register base s 20#5 (by decide)]; exact registers.output
  · rw [emitterEntry_register base s 21#5 (by decide)]; exact registers.value
  · rw [emitterEntry_register base s 22#5 (by decide)]; exact registers.descriptor
  · rw [emitterEntry_register base s 23#5 (by decide)]; exact registers.capacity
  · rw [emitterEntry_register base s 31#5 (by decide)]; exact registers.stack

theorem emitterEntry_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 648#64) : run 6 s = emitterEntry base s := by
  rw [emitterEntry]
  apply block_run base emitCallOps s code error aligned
  change r .PC s = base + 648#64 at pc
  simp [emitCallOps, Follows, Op.row, Op.effect, put, next, state_simp_rules, pc, BitVec.add_assoc]

end SszArm.Serialize
