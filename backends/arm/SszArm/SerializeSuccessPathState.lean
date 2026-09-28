import SszArm.SerializeResources
import SszArm.SerializePost
import SszArm.SerializeOwnershipResult
import SszArm.SerializeSize
import SszArm.SerializeFinishCapacity
import SszArm.SerializeEmitEntry
import SszArm.SerializeSaved

namespace SszArm.Serialize.SuccessPath

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value)
open Delimited (Span Protected MemoryFrame)
open UintCodec (widthLoad)

/-- State reached by the actual wrapper, retaining the original entry contract. -/
structure Ready (s t : ArmState) (base : BitVec 64) (desc : Desc) (value : Value) : Prop where
  code : CodeAt t base
  error : read_err t = .None
  aligned : CheckSPAlignment t
  registers : Registers t (Args.ofEntry s)
  program : t.program = s.program
  resources : Resources s t (Args.ofEntry s) desc value
  saved : Finish.SavedFrom s t
  frame : MemoryFrame (writesFor s (Args.ofEntry s) desc value) s t

def lateWrites (args : Args) (operand : NatOperand) : List Span :=
  [(args.stack.toNat - 136, 16)] ++ sizeWrites args operand

theorem late_covered (args : Args) (operand : NatOperand) :
    Covers (lateWrites args operand) (stackSpans args ++ externalSpans args) := by
  intro span member
  rcases List.mem_append.mp member with staging | scan
  · simp only [List.mem_singleton] at staging
    subst span
    exact ⟨_, by simp [stackSpans], Nat.le_refl _, Nat.le_refl _⟩
  · obtain ⟨outer, outerMember, lower, upper⟩ := size_writes_covered args operand span scan
    exact ⟨outer, List.mem_append.mpr (Or.inl outerMember), lower, upper⟩

theorem late_saved (args : Args) (operand : NatOperand) (low : 432 ≤ args.stack.toNat) :
    Protected (lateWrites args operand) (args.stack.toNat - 48) 48 := by
  right
  intro span member
  rcases List.mem_append.mp member with staging | scan
  · simp only [List.mem_singleton] at staging
    subst span
    right
    dsimp
    omega
  · cases operand with
    | small scalar => simp only [sizeWrites, List.not_mem_nil] at scan
    | large pointer limbs =>
      by_cases empty : limbs = []
      · simp only [sizeWrites, empty, ↓reduceIte, List.not_mem_nil] at scan
      · simp only [sizeWrites, empty, ↓reduceIte, List.mem_singleton] at scan
        subst span
        right
        dsimp
        omega

theorem late_subset {s : ArmState} {desc : Desc} {value : Value} (operand : NatOperand)
    (success : (measured s (Args.ofEntry s) desc value).result = .ok operand) :
    ∀ span ∈ lateWrites (Args.ofEntry s) operand, span ∈ writesFor s (Args.ofEntry s) desc value := by
  intro span member
  rcases List.mem_append.mp member with staging | scan
  · simp only [List.mem_singleton] at staging
    subst span
    simp [writesFor, afterMeasureWrites, success]
  · simp [writesFor, continuationWrites, success, scan]

/-- Run staging and arbitrary padded-Nat narrowing before inspecting either guard. -/
theorem prepare (s m : ArmState) (base : BitVec 64) (desc : Desc) (value : Value)
    (owned : Owned s (Args.ofEntry s) desc value)
    (measurement : Measured s m base desc value) (operand : NatOperand)
    (success : (measured s (Args.ofEntry s) desc value).result = .ok operand) :
    ∃ fuel t, run fuel m = t ∧ Ready s t base desc value ∧
      read_pc t = Size.destination base operand.value (Args.ofEntry s).capacity ∧
      (operand.value < 2^64 → r (.GPR 5#5) t = BitVec.ofNat 64 operand.value) := by
  let args := Args.ofEntry s
  let u := Finish.successStage base m
  have low : 432 ≤ args.stack.toNat := owned.stackLow
  have stackNat := bodySP_toNat args (by omega)
  have bound := args.stack.isLt
  have mStack : Finish.sp m = args.bodySP := measurement.registers.stack
  have planAddress : (Args.ofEntry s).plan = Finish.sp m + 24#64 := by
    rw [mStack]
    rfl
  have status : read_mem_bytes 4 (Finish.sp m + 88#64) m = 0#32 := by
    simpa only [planAddress, BitVec.add_assoc, BitVec.ofNat_add_ofNat] using
      measurement.plan_status operand success
  have stagedRun : run 10 m = u := Finish.success_stage_run base m measurement.code
    measurement.error measurement.aligned measurement.pc status
  have uStack : r (.GPR 31#5) u = args.bodySP :=
    (Finish.success_stage_register base m 31#5 (by decide)).trans mStack
  have stagedFrame : MemoryFrame [(args.stack.toNat - 136, 16)] m u := by
    have frame := Finish.success_stage_frame base m (by rw [mStack, stackNat]; omega)
    have position : (Finish.sp m).toNat + 8 = args.stack.toNat - 136 := by
      rw [mStack, stackNat]
      omega
    simpa only [position] using frame
  have stagedCover : Covers [(args.stack.toNat - 136, 16)]
      (stackSpans args ++ externalSpans args) := by
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    exact ⟨_, by simp [stackSpans], Nat.le_refl _, Nat.le_refl _⟩
  have returnedOperand := owned.measured_result_owned operand success
  have fields := measurement.plan_operand operand success
  have input : operand.At (widthLoad u) := NatDivision.operand_at_preserved stagedFrame operand
    fields.2.2 (operand_owned_of_covers stagedCover operand returnedOperand)
  have pointer : r (.GPR 8#5) u = operand.pointer := by
    exact (Finish.success_stage_fields base m).1.trans (by
      simpa only [planAddress, BitVec.add_assoc, BitVec.ofNat_add_ofNat] using fields.1)
  have payload : r (.GPR 5#5) u = operand.payload := by
    exact (Finish.success_stage_fields base m).2.1.trans (by
      simpa only [planAddress, BitVec.add_assoc, BitVec.ofNat_add_ofNat] using fields.2.1)
  have uRegisters : Registers u args := by
    refine ⟨?_, ?_, ?_, ?_, ?_, uStack⟩
    · exact (Finish.success_stage_register base m 19#5 (by decide)).trans measurement.registers.result
    · exact (Finish.success_stage_register base m 20#5 (by decide)).trans measurement.registers.output
    · exact (Finish.success_stage_register base m 21#5 (by decide)).trans measurement.registers.value
    · exact (Finish.success_stage_register base m 22#5 (by decide)).trans measurement.registers.descriptor
    · exact (Finish.success_stage_register base m 23#5 (by decide)).trans measurement.registers.capacity
  have uCode : CodeAt u base := measurement.code.congr (Finish.success_stage_program base m)
  have uError : read_err u = .None := (Finish.success_stage_error base m).trans measurement.error
  have uAligned : CheckSPAlignment u := CheckSPAlignment_of_r_sp_aligned
    (uStack.trans mStack.symm) (BoolCodec.stack_aligned m measurement.aligned)
  have scratchCover : Covers [((r (.GPR 31#5) u).toNat - 16, 16)]
      (stackSpans args ++ externalSpans args) := by
    rw [uStack, stackNat]
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    refine ⟨(args.stack.toNat - 160, 16), by simp [stackSpans], ?_, ?_⟩ <;> dsimp <;> omega
  obtain ⟨fuel, t, executed, post⟩ := Size.program_correct u base operand args.capacity
    uCode uError uAligned (Finish.success_stage_pc base m status) pointer payload uRegisters.capacity
    input (operand_owned_of_covers scratchCover operand returnedOperand)
    (by rw [uStack, stackNat]; omega)
  have scanFrame : MemoryFrame (sizeWrites args operand) u t := by
    have footprint := post.footprint
    cases operand with
    | small scalar => exact footprint
    | large address limbs =>
      cases limbs with
      | nil => exact footprint
      | cons first rest =>
        simpa only [Size.actualWrites, Size.writes, sizeWrites, List.cons_ne_nil, ↓reduceIte,
          uStack, stackNat, Nat.sub_sub] using footprint
  have lateFrame : MemoryFrame (lateWrites args operand) m t :=
    (stagedFrame.weaken (fun _ member => List.mem_append.mpr (Or.inl member))).trans
      (scanFrame.weaken (fun _ member => List.mem_append.mpr (Or.inr member)))
  have tRegisters : Registers t args := by
    refine ⟨?_, ?_, ?_, ?_, ?_, post.frame.sp.trans uStack⟩
    · exact (post.frame.registers 19#5 (by decide)).trans uRegisters.result
    · exact (post.frame.registers 20#5 (by decide)).trans uRegisters.output
    · exact (post.frame.registers 21#5 (by decide)).trans uRegisters.value
    · exact (post.frame.registers 22#5 (by decide)).trans uRegisters.descriptor
    · exact (post.frame.registers 23#5 (by decide)).trans uRegisters.capacity
  have saved : Finish.SavedFrom s t := measurement.savedFrom.of_frame lateFrame
    (tRegisters.stack.trans mStack.symm) (by rw [mStack, stackNat]; omega) (by
      have position : (Finish.sp m).toNat + 96 = args.stack.toNat - 48 := by
        rw [mStack, stackNat]
        omega
      rw [position]
      exact late_saved args operand low) (by
      intro reg lower upper outside
      have stageOutside : reg ∉ [5#5, 8#5, 9#5, 10#5, 11#5, 12#5] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        bv_omega
      have scanOutside : reg ∉ [5#5, 9#5, 10#5, 11#5] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        bv_omega
      exact (post.frame.registers reg scanOutside).trans
        (Finish.success_stage_register base m reg stageOutside)) (by
      intro reg lower upper
      rw [post.frame.vectors, Finish.success_stage_vector])
  refine ⟨10 + fuel, t, ?_, ?_, post.pc, post.payload⟩
  · rw [run_plus, stagedRun, executed]
  · refine ⟨post.frame.code uCode, post.frame.error.trans uError, post.frame.aligned uAligned,
      tRegisters, post.frame.program.trans ((Finish.success_stage_program base m).trans measurement.program),
      Resources.of_frame owned measurement.resources lateFrame (late_covered args operand), saved, ?_⟩
    exact (measurement.frame.weaken (by
      intro span member
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl member))))).trans
      (lateFrame.weaken (late_subset operand success))

end SszArm.Serialize.SuccessPath
