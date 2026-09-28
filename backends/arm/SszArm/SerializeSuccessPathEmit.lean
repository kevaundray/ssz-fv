import SszArm.SerializeSuccessPathState
import SszArm.EmitProgram

namespace SszArm.Serialize.SuccessPath

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value)
open Delimited (Protected MemoryFrame)
open UintCodec (widthLoad)

theorem saved_protected_emit {s : ArmState} {args : Args} {desc : Desc} {value : Value}
    (owned : Owned s args desc value) (count : Nat) (fitting : count ≤ args.capacity.toNat) :
    Protected (Emit.writesFor (args.emit count) count) (args.stack.toNat - 48) 48 := by
  have low := owned.stackLow
  have stackNat := bodySP_toNat args (by omega)
  have saveMember : (args.stack.toNat - 48, 48) ∈ stackSpans args := by simp [stackSpans]
  right
  intro span member
  rcases List.mem_append.mp member with body | output
  · rcases List.mem_append.mp body with stack | result
    · simp only [Emit.stackWrites, Args.emit, stackNat, List.mem_cons, List.not_mem_nil,
        or_false] at stack
      rcases stack with rfl | rfl <;> right <;> dsimp <;> omega
    · rcases owned.resultStack with empty | apart
      · change 72 = 0 at empty
        omega
      · have separate := apart _ saveMember
        simp only [Args.emit, List.mem_cons, List.not_mem_nil, or_false] at result
        rcases result with rfl | rfl <;> dsimp at separate ⊢ <;> omega
  · split at output
    · simp only [List.not_mem_nil] at output
    · simp only [Args.emit, List.mem_singleton] at output
      subst span
      rcases owned.outputStack with empty | apart
      · dsimp at empty ⊢
        omega
      · have separate := apart _ saveMember
        dsimp at separate ⊢
        omega

/-- The actual six-instruction call setup passes the measured count as capacity;
    the emitter executes in the very same ordered program and returns to PC672. -/
theorem emission_correct (s t : ArmState) (base : BitVec 64) (desc : Desc) (value : Value)
    (owned : Owned s (Args.ofEntry s) desc value) (ready : Ready s t base desc value)
    (operand : NatOperand)
    (success : (measured s (Args.ofEntry s) desc value).result = .ok operand)
    (representable : operand.value < 2^64)
    (fitting : operand.value ≤ (Args.ofEntry s).capacity.toNat)
    (pc : read_pc t = base + 648#64)
    (payload : r (.GPR 5#5) t = BitVec.ofNat 64 operand.value) :
    ∃ fuel u, run fuel t = u ∧ Post s u desc value := by
  let args := Args.ofEntry s
  let entry := emitterEntry base t
  have entryArgs : Emit.Args.ofEntry entry = args.emit operand.value :=
    emitterEntry_args base t args operand.value ready.registers payload
  have entryFrame : MemoryFrame [] t entry := by
    intro address outside
    exact congrFun (emitterEntry_memory base t) address
  have entryHistory : MemoryFrame (writesFor s args desc value) s entry :=
    ready.frame.trans (entryFrame.weaken (by simp))
  have observations := frame_of_covers entryHistory (writesFor_covered owned)
  have expected := expected_of_measured s args desc value owned.physical operand success
  have emitterOwned : Emit.Owned entry (Emit.Args.ofEntry entry) desc value operand.value := by
    rw [entryArgs]
    exact owned.emit_of_observations operand.value expected representable fitting
      (descriptor_preserved owned observations) (value_preserved owned observations)
      (backing_preserved owned observations)
  have entryCode : CodeAt entry base := ready.code.congr (emitterEntry_program base t)
  have entryError : read_err entry = .None := (emitterEntry_error base t).trans ready.error
  obtain ⟨emitFuel, emitted⟩ := Emit.program_correct entry (base + emitOffset) desc value operand.value
    emitterOwned entryCode.emit entryError (emitterEntry_aligned base t ready.aligned)
    (emitterEntry_pc base t)
  let v := run emitFuel entry
  let u := Finish.returned v
  have emittedFrame : MemoryFrame (Emit.writesFor (args.emit operand.value) operand.value) entry v := by
    simpa only [entryArgs] using emitted.frame
  have throughEmit : MemoryFrame (Emit.writesFor (args.emit operand.value) operand.value) t v :=
    (entryFrame.weaken (by simp)).trans emittedFrame
  have vStack : r (.GPR 31#5) v = r (.GPR 31#5) t := emitted.returned.sp.trans
    (emitterEntry_register base t 31#5 (by decide))
  have low : 432 ≤ args.stack.toNat := owned.stackLow
  have stackNat := bodySP_toNat args (by omega)
  have stackHigh : (Finish.sp t).toNat + 144 ≤ 2^64 := by
    rw [show Finish.sp t = args.bodySP from ready.registers.stack, stackNat]
    have bound := args.stack.isLt
    omega
  have saved : Finish.SavedFrom s v := ready.saved.of_frame throughEmit vStack stackHigh (by
    have position : (Finish.sp t).toNat + 96 = args.stack.toNat - 48 := by
      rw [show Finish.sp t = args.bodySP from ready.registers.stack, stackNat]
      omega
    rw [position]
    exact saved_protected_emit owned operand.value fitting) (by
    intro reg lower upper outside
    have entryOutside : reg ∉ [0#5, 1#5, 2#5, 3#5, 4#5, 30#5] := by
      have notLR : reg ≠ 30#5 := by
        intro same
        subst reg
        simp at outside
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      bv_omega
    exact (emitted.returned.registers reg lower upper).trans
      (emitterEntry_register base t reg entryOutside)) (by
    intro reg lower upper
    exact (emitted.returned.vectors reg lower upper).trans
      (congrArg (fun bits : BitVec 128 => bits.setWidth 64) (emitterEntry_vector base t reg)))
  have vProgram : v.program = s.program := emitted.returned.program.trans
    ((emitterEntry_program base t).trans ready.program)
  have vCode : CodeAt v base := entryCode.congr emitted.returned.program
  have vAligned : CheckSPAlignment v := CheckSPAlignment_of_r_sp_aligned vStack
    (BoolCodec.stack_aligned t ready.aligned)
  have vPC : read_pc v = base + 672#64 := emitted.returned.pc.trans (emitterEntry_lr base t)
  have returnRun : run 5 v = u := Finish.return_run .emitted base v vCode
    emitted.returned.error vAligned vPC
  have returned : Emit.Returned s u := Finish.returned_original s v saved vProgram emitted.returned.error
  have returnFrame : MemoryFrame [] v u := by
    intro address outside
    exact congrFun (Finish.returned_memory v) address
  have lastFrame : MemoryFrame (Emit.writesFor (args.emit operand.value) operand.value) t u :=
    throughEmit.trans (returnFrame.weaken (by simp))
  have resources := Resources.of_frame owned ready.resources lastFrame
    (emit_writes_covered_external args operand.value owned.stackLow fitting)
  have finalFrame : MemoryFrame (writesFor s args desc value) s u := ready.frame.trans
    (lastFrame.weaken (by
      intro span member
      exact List.mem_append.mpr (Or.inr (by
        simp only [continuationWrites, success, representable, fitting, and_self, ↓reduceIte]
        exact List.mem_append.mpr (Or.inr member)))))
  have outcomeEq := outcome_of_success s args desc value operand success representable fitting
  have loadEq : widthLoad u = widthLoad v := by
    funext address bytes
    simp only [u, Finish.returned, widthLoad, state_simp_rules]
  have resultLength : read_mem_bytes 8 args.result v = BitVec.ofNat 64 operand.value := by
    simpa only [entryArgs, Args.emit] using emitted.length
  have resultStatus : read_mem_bytes 4 (args.result + 64#64) v = 0#32 := by
    simpa only [entryArgs, Args.emit] using emitted.status
  refine ⟨6 + emitFuel + 5, u, ?_, ?_⟩
  · rw [run_plus, run_plus, emitterEntry_run t base ready.code ready.error ready.aligned pc]
    exact returnRun
  · apply post_of_return s u desc value owned returned
    · rw [outcomeEq]
      change widthLoad u args.result.toNat 8 = some operand.value ∧
        widthLoad u (args.result.toNat + 64) 4 = some 0
      rw [loadEq]
      constructor
      · simp only [widthLoad, BitVec.ofNat_toNat, BitVec.setWidth_eq,
          resultLength, BitVec.toNat_ofNat, Nat.mod_eq_of_lt representable]
      · simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
          congrArg (fun bits : BitVec 32 => some bits.toNat) resultStatus
    · rw [outcomeEq]
      exact resources.cursor
    · exact resources.header
    · rw [outcomeEq]
      exact resources.written
    · rw [outcomeEq, loadEq]
      simpa only [entryArgs, Args.emit] using emitted.bytes
    · exact finalFrame

end SszArm.Serialize.SuccessPath
