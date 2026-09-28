import SszArm.EmitUintLoopInduction

namespace SszArm.Emit.Uint

open SszNative (NatOperand)

def numberEntryOps : NatOperand → List ByteOp
  | .small _ => [.p916, .p920, .p924]
  | .large _ _ => [.p916, .p920, .p924, .p928, .p932]

@[irreducible] def numberEntered (s : ArmState) (base : BitVec 64) : NatOperand → ArmState
  | .small word => w .PC (base + 936#64)
      (w (.GPR 10#5) 0#64 (w (.GPR 8#5) word (w (.GPR 9#5) 0#64 s)))
  | .large pointer words => w .PC (base + 1132#64)
      (w (.GPR 11#5) 0#64 (w (.GPR 10#5) 0#64
        (w (.GPR 8#5) (BitVec.ofNat 64 words.length) (w (.GPR 9#5) pointer s))))

theorem number_entry_run {s : ArmState} {args : Args} {width number : NatOperand} {size : Nat}
    (base : BitVec 64) (owned : Owned s args (.uint width) (.uint number) size)
    (registers : BodyRegisters s args) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 916#64) :
    run (numberEntryOps number).length s = numberEntered s base number := by
  obtain ⟨pointerRead, payloadRead⟩ := number_pair owned
  have position : r .PC s = base + 916#64 := pc
  cases number with
  | small word =>
    have follows : ByteFollows base (numberEntryOps (.small word)) s := by
      simp [numberEntryOps, ByteFollows, ByteOp.row, ByteOp.effect, put, next, Dispatch.next,
        state_simp_rules, position, registers.value, pointerRead, NatOperand.pointer,
        BitVec.add_assoc]
    rw [byte_run base _ s code error aligned follows]
    simp [byteBlock, numberEntryOps, ByteOp.effect, put, next, Dispatch.next, numberEntered,
      state_simp_rules, registers.value, pointerRead, payloadRead, NatOperand.pointer,
      NatOperand.payload, NatAdd.load_gpr_pc, w_of_w_shadow]
  | large pointer words =>
    have input := owned.operand_at (.large pointer words) (by simp [descriptorOperands, valueOperands])
    have nonzero : pointer ≠ 0#64 := by
      have positive := input.1
      intro zero
      simp only [zero, BitVec.toNat_ofNat] at positive
      omega
    have follows : ByteFollows base (numberEntryOps (.large pointer words)) s := by
      simp [numberEntryOps, ByteFollows, ByteOp.row, ByteOp.effect, put, next, Dispatch.next,
        state_simp_rules, position, registers.value, pointerRead, NatOperand.pointer,
        nonzero, BitVec.add_assoc]
    rw [byte_run base _ s code error aligned follows]
    simp [byteBlock, numberEntryOps, ByteOp.effect, put, next, Dispatch.next, numberEntered,
      state_simp_rules, registers.value, pointerRead, payloadRead, NatOperand.pointer,
      NatOperand.payload, nonzero, NatAdd.load_gpr_pc, w_of_w_shadow]

@[simp] theorem numberEntered_memory (s : ArmState) (base : BitVec 64) (number : NatOperand) :
    (numberEntered s base number).mem = s.mem := by cases number <;> simp [numberEntered, state_simp_rules]

@[simp] theorem numberEntered_register (s : ArmState) (base : BitVec 64) (number : NatOperand)
    (reg : BitVec 5) (outside : reg ∉ [8#5, 9#5, 10#5, 11#5]) :
    r (.GPR reg) (numberEntered s base number) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  cases number <;> simp [numberEntered, state_simp_rules, outside.1,
    outside.2.1, outside.2.2.1, outside.2.2.2]

theorem numberEntered_frame (s : ArmState) (base : BitVec 64) (number : NatOperand) (args : Args) (size : Nat) :
    Frame s (numberEntered s base number) args size := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases number <;> simp [numberEntered, state_simp_rules]
  · cases number <;> simp [numberEntered, state_simp_rules]
  · intro reg outside
    apply numberEntered_register
    simp_all
  · intro reg
    cases number <;> simp [numberEntered, state_simp_rules]
  · intro address outside
    rw [numberEntered_memory]

theorem numberEntered_small (s : ArmState) (base : BitVec 64) (word : BitVec 64) (size : Nat)
    (length : r (.GPR 1#5) s = BitVec.ofNat 64 size) :
    read_pc (numberEntered s base (.small word)) = base + 936#64 ∧
      SmallRegisters (numberEntered s base (.small word)) word 0 size := by
  constructor
  · simp [numberEntered, state_simp_rules]
  · constructor <;> simp [numberEntered, state_simp_rules, length]

theorem numberEntered_large (s : ArmState) (base : BitVec 64) (pointer : BitVec 64)
    (words : List (BitVec 64)) (size : Nat)
    (length : r (.GPR 1#5) s = BitVec.ofNat 64 size) :
    read_pc (numberEntered s base (.large pointer words)) = base + 1132#64 ∧
      LargeRegisters (numberEntered s base (.large pointer words)) pointer words 0 size := by
  constructor
  · simp [numberEntered, state_simp_rules]
  · constructor <;> simp [numberEntered, state_simp_rules, length]

end SszArm.Emit.Uint
