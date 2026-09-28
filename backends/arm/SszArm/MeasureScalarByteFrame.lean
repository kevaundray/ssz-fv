import SszArm.MeasureScalarByteSetup
import SszArm.MeasureErrorWritersProduced

namespace SszArm.Measure.Scalar.Bytes

open Delimited (MemoryFrame)
open SszNative (NatOperand)

/-- Byte leaves may repurpose X20/X21 but never touch the caller's immutable
activation, its preserved integer/vector registers, or memory outside the real
sixteen-byte lowering slot before the selected writer. -/
structure Frame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  output : r (.GPR 19#5) t = r (.GPR 19#5) s
  stack : r (.GPR 31#5) t = r (.GPR 31#5) s
  registers : ∀ reg : BitVec 5, reg ∈ [18#5, 27#5, 28#5, 29#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : ∀ address : BitVec 64,
    address.toNat < (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ address.toNat → t.mem address = s.mem address

theorem Frame.refl (s : ArmState) : Frame s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem Frame.of_narrow {s t : ArmState} (frame : NatNarrow.Frame s t) : Frame s t := by
  refine ⟨frame.program, frame.error, frame.registers _ (by decide), frame.sp,
    ?_, frame.vectors, frame.memory⟩
  intro reg member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> exact frame.registers _ (by decide)

theorem Frame.trans {s t u : ArmState} (first : Frame s t) (second : Frame t u) : Frame s u := by
  refine ⟨second.program.trans first.program, second.error.trans first.error,
    second.output.trans first.output, second.stack.trans first.stack,
    fun reg member => (second.registers reg member).trans (first.registers reg member),
    fun reg => (second.vectors reg).trans (first.vectors reg), ?_⟩
  intro address outside
  exact (second.memory address (by simpa only [first.stack] using outside)).trans
    (first.memory address outside)

theorem Frame.aligned {s t : ArmState} (frame : Frame s t) (aligned : CheckSPAlignment s) :
    CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, frame.stack] using aligned

theorem Frame.memory_frame {s t : ArmState} (frame : Frame s t) (writes : List Delimited.Span)
    (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat)
    (slot : ((r (.GPR 31#5) s).toNat - 16, 16) ∈ writes) : MemoryFrame writes s t := by
  intro address outside
  have separate := outside _ slot
  apply frame.memory
  simp only [Prod.fst, Prod.snd] at separate
  omega

theorem Frame.owned {s t : ArmState} {args : Args} {kind : Kind} {cap : NatOperand}
    {bytes : Ssz.Bytes} (frame : Frame s t) (owned : Owned s args (kind.desc cap) (.bytes bytes))
    (stack : r (.GPR 31#5) s = args.bodySP) : Owned t args (kind.desc cap) (.bytes bytes) := by
  have low := owned.stackLow
  have position : (r (.GPR 31#5) s).toNat - 16 = args.stack.toNat - 288 := by
    rw [stack, Args.bodySP]; bv_omega
  exact owned.of_local_frame (frame.memory_frame _ (by rw [stack, Args.bodySP]; bv_omega)
    (by simp [position, localWrites, stackWrites, bodyStackWrites]))

theorem Frame.prepend {s u t : ArmState} {args : Args} {kind : Kind} {cap : NatOperand}
    {bytes : Ssz.Bytes} {base : BitVec 64} (frame : Frame s u)
    (owned : Owned s args (kind.desc cap) (.bytes bytes))
    (stack : r (.GPR 31#5) s = args.bodySP)
    (post : Produced u t args (kind.desc cap) (.bytes bytes) base) :
    Produced s t args (kind.desc cap) (.bytes bytes) base := by
  have low := owned.stackLow
  have position : (r (.GPR 31#5) s).toNat - 16 = args.stack.toNat - 288 := by
    rw [stack, Args.bodySP]; bv_omega
  have localFrame := frame.memory_frame (localWrites args (outcome s args (kind.desc cap) (.bytes bytes)))
    (by rw [stack, Args.bodySP]; bv_omega)
    (by simp [position, localWrites, stackWrites, bodyStackWrites])
  have measured := outcome_eq_of_arena_eq (desc := kind.desc cap) (value := .bytes bytes)
    (arenaOf_eq_of_local_frame owned localFrame)
  have first := frame.memory_frame (bodyWrites args (outcome s args (kind.desc cap) (.bytes bytes)))
    (by rw [stack, Args.bodySP]; bv_omega) (by simp [position, bodyWrites, bodyStackWrites])
  have second : MemoryFrame (bodyWrites args (outcome s args (kind.desc cap) (.bytes bytes))) u t := by
    simpa only [measured] using post.frame
  apply Produced.of_no_calls owned (byte_calls kind s args cap bytes owned.physical)
    (byte_used kind s args cap bytes owned.physical) post.pc (post.program.trans frame.program)
    post.error post.stack
  · simpa only [measured] using post.result
  · exact first.trans second
  · intro reg member
    exact (post.registers reg member).trans (frame.registers reg member)
  · intro reg lower upper
    rw [post.vectors reg lower upper, frame.vectors]

end SszArm.Measure.Scalar.Bytes
