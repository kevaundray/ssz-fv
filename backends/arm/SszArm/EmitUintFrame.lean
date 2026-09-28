import SszArm.EmitUintOwned

namespace SszArm.Emit.Uint

open Delimited (MemoryFrame)

structure Frame (s t : ArmState) (args : Args) (size : Nat) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [1#5, 8#5, 9#5, 10#5, 11#5, 12#5, 13#5, 14#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : MemoryFrame (bodyWrites args size) s t

theorem Frame.refl (s : ArmState) (args : Args) (size : Nat) : Frame s s args size :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem Frame.trans {s t u : ArmState} {args : Args} {size : Nat}
    (first : Frame s t args size) (second : Frame t u args size) : Frame s u args size :=
  ⟨second.program.trans first.program, second.error.trans first.error,
   fun reg outside => (second.registers reg outside).trans (first.registers reg outside),
   fun reg => (second.vectors reg).trans (first.vectors reg),
   fun address outside => (second.memory address outside).trans (first.memory address outside)⟩

theorem Frame.bodyRegisters {s t : ArmState} {args : Args} {size : Nat}
    (frame : Frame s t args size) (registers : BodyRegisters s args) : BodyRegisters t args := by
  constructor
  · exact (frame.registers _ (by decide)).trans registers.result
  · exact (frame.registers _ (by decide)).trans registers.output
  · exact (frame.registers _ (by decide)).trans registers.capacity
  · exact (frame.registers _ (by decide)).trans registers.value
  · exact (frame.registers _ (by decide)).trans registers.stack

theorem Frame.code {s t : ArmState} {args : Args} {size : Nat}
    (frame : Frame s t args size) {base : BitVec 64} (code : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, frame.program] using code

theorem Frame.aligned {s t : ArmState} {args : Args} {size : Nat}
    (frame : Frame s t args size) (aligned : CheckSPAlignment s) : CheckSPAlignment t := by
  have sp := frame.registers 31#5 (by decide)
  simpa only [CheckSPAlignment, state_simp_rules, sp] using aligned

theorem Frame.owned {s t : ArmState} {args : Args} {width number : SszNative.NatOperand} {size : Nat}
    (frame : Frame s t args size) (owned : Owned s args (.uint width) (.uint number) size) :
    Owned t args (.uint width) (.uint number) size :=
  owned.of_frame (frame.memory.weaken (bodyWrites_subset args size))

theorem narrow_frame {s t : ArmState} {args : Args} {width number : SszNative.NatOperand}
    {size : Nat} (owned : Owned s args (.uint width) (.uint number) size)
    (registers : BodyRegisters s args) (frame : NatNarrow.Frame s t) : Frame s t args size := by
  refine ⟨frame.program, frame.error, ?_, frame.vectors, ?_⟩
  · intro reg outside
    apply frame.registers
    intro member
    apply outside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    rcases member with rfl | rfl | rfl | rfl | rfl <;> simp
  · apply frame.memoryFrame (bodyWrites args size) _ (body_stack_safe owned registers)
    have low := owned.stackLow
    have slot : (r (.GPR 31#5) s).toNat - 16 = args.stack.toNat - 176 := by
      rw [registers.stack]
      unfold Args.bodySP
      bv_omega
    simp [slot, bodyWrites]

end SszArm.Emit.Uint
