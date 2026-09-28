import SszArm.MeasureBitsReturnedPost

namespace SszArm.Measure.Bits

open UintCodec (widthLoad)
open Propagation

theorem returned_success_executes (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1916#64) (space : Result.SuccessSpace s)
    (operand : SszNative.NatOperand)
    (input : SszNative.NatArithmetic.AddResultAt (widthLoad s)
      ((r (.GPR 31#5) s).toNat + 120) (.ok operand))
    (borrowed : NatDivision.OperandOwned (Result.successWrites s) operand) :
    ∃ t, run 36 s = t ∧ ReturnedPost s t base (.ok operand) (Result.successWrites s) := by
  obtain ⟨⟨pointer, payload, limbs⟩, status⟩ := input
  have first : read_mem_bytes 8 (r (.GPR 31#5) s + 120#64) s = operand.pointer :=
    BitVector.read_of_observe_offset s (r (.GPR 31#5) s) 120 8 operand.pointer pointer
  have second : read_mem_bytes 8 (r (.GPR 31#5) s + 128#64) s = operand.payload :=
    BitVector.read_of_observe_offset s (r (.GPR 31#5) s) 128 8 operand.payload
      (by simpa only [Nat.add_assoc] using payload)
  have flag : read_mem_bytes 4 (r (.GPR 31#5) s + 184#64) s = 0#32 :=
    BitVector.read_of_observe_offset s (r (.GPR 31#5) s) 184 4 0#32
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, (show (0#32).toNat = 0 by decide)] using status)
  let p := Stage.returned.result s base
  let t := Result.successResult p base
  have before : run 3 s = p := executes .returned s base code error aligned pc
  have output : r (.GPR 19#5) p = r (.GPR 19#5) s := stage_register .returned s base _ (by decide)
  have stack : r (.GPR 31#5) p = r (.GPR 31#5) s := stage_sp .returned s base
  have sameWrites : Result.successWrites p = Result.successWrites s := by
    simp only [Result.successWrites, output, stack]
  have pSpace : Result.SuccessSpace p := by
    obtain ⟨stackLow, bound, fields, flagSeparate⟩ := space
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [stack] using stackLow
    · simpa only [output] using bound
    · simpa only [output, stack] using fields
    · simpa only [output, stack] using flagSeparate
  have pAligned : CheckSPAlignment p := by
    simpa only [CheckSPAlignment, state_simp_rules, stack] using aligned
  have after : run 33 p = t := Result.success_run p base
    (code.congr (stage_program .returned s base)) ((stage_error .returned s base).trans error)
    pAligned (by simp [p, Stage.result, state_simp_rules, flag])
  have stored := Result.success_at p base pSpace operand
    (by simp [p, Stage.result, state_simp_rules, first])
    (by simp [p, Stage.result, state_simp_rules, second])
    (by rw [Emit.load_eq_of_mem_eq (returned_memory s base)]; exact limbs)
    (by simpa only [sameWrites] using borrowed)
  have frame := Result.success_frame p base pSpace
  refine ⟨t, by rw [show 36 = 3 + 33 by decide, run_plus, before, after],
    Result.success_pc p base,
    (Result.success_program p base).trans (stage_program .returned s base),
    (Result.success_error p base).trans ((stage_error .returned s base).trans error),
    (Result.success_sp p base).trans stack, ?_, ?_, ?_, ?_⟩
  · simpa only [output] using stored
  · intro address outside
    exact (frame address (by simpa only [sameWrites] using outside)).trans
      (congrFun (returned_memory s base) address)
  · intro reg member
    have keep : reg ≠ 8#5 ∧ reg ≠ 9#5 ∧ reg ≠ 10#5 ∧ reg ∉ Stage.returned.clobbers := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    exact (Result.success_register p base reg keep.1 keep.2.1 keep.2.2.1).trans
      (stage_register .returned s base reg keep.2.2.2)
  · intro reg low high
    exact congrArg (fun word : BitVec 128 => word.setWidth 64)
      ((Result.success_vector p base reg).trans (stage_vector .returned s base reg))

end SszArm.Measure.Bits
