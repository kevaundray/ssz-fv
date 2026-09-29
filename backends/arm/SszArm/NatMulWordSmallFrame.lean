import SszArm.NatMulWordHighFrame
import SszArm.NatMulWordScanEntry
import SszArm.NatMulWordReturnValues
import SszArm.NatMulWordReturnError
import SszArm.NatMulWordReserveModel

namespace SszArm.NatMulWord

open UintCodec (widthLoad)
open Delimited (MemoryFrame Protected Returned)

/-- Registers retained throughout the significant-one-word path. -/
structure SmallABI (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5,
    reg ∉ [1#5, 2#5, 8#5, 9#5, 10#5, 11#5, 12#5, 13#5, 14#5, 15#5, 16#5, 17#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s

structure SmallFrame (s t : ArmState) : Prop extends SmallABI s t where
  memory : MemoryFrame [((r (.GPR 31#5) s).toNat - 48, 48)] s t

theorem SmallABI.sp {s t : ArmState} (h : SmallABI s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := h.registers _ (by decide)

theorem SmallABI.out {s t : ArmState} (h : SmallABI s t) :
    r (.GPR 0#5) t = r (.GPR 0#5) s := h.registers _ (by decide)

theorem SmallABI.arena {s t : ArmState} (h : SmallABI s t) :
    r (.GPR 4#5) t = r (.GPR 4#5) s := h.registers _ (by decide)

theorem SmallABI.trans {s t u : ArmState} (h : SmallABI s t) (k : SmallABI t u) : SmallABI s u :=
  ⟨k.program.trans h.program, k.error.trans h.error,
    fun reg hr => (k.registers reg hr).trans (h.registers reg hr),
    fun reg => (k.vectors reg).trans (h.vectors reg)⟩

theorem SmallFrame.trans {s t u : ArmState} (h : SmallFrame s t) (k : SmallFrame t u) : SmallFrame s u :=
  ⟨h.toSmallABI.trans k.toSmallABI, h.memory.trans (by simpa only [h.sp] using k.memory)⟩

theorem SmallABI.code {s t : ArmState} (h : SmallABI s t) {base : BitVec 64}
    (code : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, h.program] using code

theorem SmallABI.aligned {s t : ArmState} (h : SmallABI s t)
    (aligned : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, h.sp] using aligned

theorem SmallABI.return_owned {s t : ArmState} (h : SmallABI s t)
    (owned : ReturnOwned s) : ReturnOwned t := by
  exact ⟨by simpa only [h.sp] using owned.stack,
    by simpa only [h.out] using owned.output,
    by simpa only [h.sp, h.out] using owned.separate⟩

theorem SmallABI.returned {s t u : ArmState} (h : SmallABI s t)
    (returned : Returned t u) : Returned s u := by
  refine ⟨returned.pc.trans (h.registers _ (by decide)), returned.error,
    returned.sp.trans h.sp, ?_, ?_⟩
  · intro reg low high
    apply (returned.registers reg low high).trans
    apply h.registers
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    repeat' apply And.intro
    all_goals bv_omega
  · intro reg low high
    exact (returned.vectors reg low high).trans
      (congrArg (fun x : BitVec 128 => x.setWidth 64) (h.vectors reg))

theorem ScanFrame.small {s t : ArmState} (h : ScanFrame s t)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) : SmallFrame s t := by
  refine ⟨⟨h.program, h.error, ?_, h.vectors⟩, ?_⟩
  · intro reg keep
    apply h.registers
    simp_all only [List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true]
  · intro a outside
    have work := outside ((r (.GPR 31#5) s).toNat - 48, 48) (by simp)
    apply h.memory
    omega

theorem small_high_frame (s : ArmState) (base : BitVec 64)
    (stack : 48 ≤ (r (.GPR 31#5) s).toNat) :
    SmallFrame s (highCompleted .small s base) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, high_completed_frame .small s base stack⟩
  · simp only [highCompleted, block_program]
  · simp only [highCompleted, block_error]
  · intro reg keep
    apply high_completed_registers .small s base stack reg
    simp_all [HighSite.destination]
  · intro reg
    unfold highCompleted
    repeat' rw [Reserve.block_preserves (r (.SFP reg)) base _
      (fun op _ t => op.sfp base t reg)]

theorem Reserve.Checkpoint.small {s t : ArmState} (h : Reserve.Checkpoint s t) : SmallFrame s t := by
  refine ⟨⟨h.frame.program, h.frame.error, ?_, h.frame.vectors⟩, ?_⟩
  · intro reg keep
    apply h.frame.registers
    simp_all only [List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true]
  · intro a _
    exact congrFun h.memory a

theorem small_stack_local (s : ArmState) (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand) :
    ((r (.GPR 31#5) s).toNat - 48, 48) ∈ localWrites s result := by
  cases result.result <;> simp [localWrites]

theorem small_local_writes (s : ArmState) (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand) :
    ∀ span ∈ localWrites s result, span ∈ writesFor s result := by
  intro span member
  cases allocation : result.allocation with
  | none => simpa only [writesFor, allocation] using member
  | some reservation =>
    simp only [writesFor, allocation, List.mem_append]
    exact Or.inl member

theorem SmallFrame.full {s t : ArmState} (h : SmallFrame s t)
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand) :
    MemoryFrame (writesFor s result) s t := by
  apply h.memory.weaken
  intro span member
  simp only [List.mem_singleton] at member
  subst span
  exact small_local_writes s result _ (small_stack_local s result)

theorem SmallFrame.header {s t : ArmState} {operand : SszNative.NatOperand} {factor : BitVec 64}
    (h : SmallFrame s t) (owned : Owned s operand factor) (offset : Nat) (bound : offset + 8 ≤ 24) :
    read_mem_bytes 8 (r (.GPR 4#5) t + BitVec.ofNat 64 offset) t =
      read_mem_bytes 8 (r (.GPR 4#5) s + BitVec.ofNat 64 offset) s := by
  have physical := owned.arenaBound
  have address : (r (.GPR 4#5) s + BitVec.ofNat 64 offset).toNat = (r (.GPR 4#5) s).toNat + offset := by
    bv_omega
  have arenaProtected : Protected [((r (.GPR 31#5) s).toNat - 48, 48)] (r (.GPR 4#5) s).toNat 24 := by
    rcases owned.arenaLocal with empty | apart
    · exact Or.inl empty
    · right
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      exact apart _ (small_stack_local s (outcome s operand factor))
  rw [h.arena]
  exact h.memory.read _ 8 (by rw [address]; omega)
    (by rw [address]; exact arenaProtected.subspan offset 8 bound)

theorem small_unchanged_post (s t : ArmState) (operand : SszNative.NatOperand) (factor : BitVec 64)
    (owned : Owned s operand factor) (result : Except SszNative.NatArithmetic.Failure SszNative.NatOperand)
    (model : outcome s operand factor = SszNative.NatArithmetic.unchanged (arenaOf s).used result)
    (returned : Returned s t)
    (image : SszNative.NatArithmetic.AddResultAt (widthLoad t) (r (.GPR 0#5) s).toNat result)
    (frame : MemoryFrame (writesFor s (outcome s operand factor)) s t) : Post s t operand factor := by
  have arena : Protected (writesFor s (outcome s operand factor)) (r (.GPR 4#5) s).toNat 24 := by
    simpa only [writesFor, model, SszNative.NatArithmetic.unchanged] using owned.arenaLocal
  have physical := owned.arenaBound
  have capAddress : (r (.GPR 4#5) s + 8#64).toNat = (r (.GPR 4#5) s).toNat + 8 := by bv_omega
  have usedAddress : (r (.GPR 4#5) s + 16#64).toNat = (r (.GPR 4#5) s).toNat + 16 := by bv_omega
  have baseSame := frame.read (r (.GPR 4#5) s) 8 (by omega)
    (by simpa using arena.subspan 0 8 (by decide))
  have capSame := frame.read (r (.GPR 4#5) s + 8#64) 8 (by rw [capAddress]; omega)
    (by rw [capAddress]; exact arena.subspan 8 8 (by decide))
  have usedSame := frame.read (r (.GPR 4#5) s + 16#64) 8 (by rw [usedAddress]; omega)
    (by rw [usedAddress]; exact arena.subspan 16 8 (by decide))
  refine ⟨returned, ?_, ?_, ?_, frame,
    NatAdd.operand_preserved frame operand owned.operandAt owned.inputOwned, baseSame, capSame⟩
  · simpa only [model, SszNative.NatArithmetic.unchanged] using image
  · intro reservation allocated
    simp [model, SszNative.NatArithmetic.unchanged] at allocated
  · simp only [model, SszNative.NatArithmetic.unchanged, arenaOf, usedSame]

end SszArm.NatMulWord
