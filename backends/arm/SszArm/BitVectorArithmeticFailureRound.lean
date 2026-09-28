import SszArm.BitVectorArithmeticFailureCommon

namespace SszArm.BitVector.ArithmeticFailure

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

def roundResult (t : ArmState) (base : BitVec 64) : ArmState :=
  ErrorTail.Tail.tag.result (ErrorTail.Tail.round.result t base) base

private theorem round_fields (t : ArmState) (base : BitVec 64)
    (physical : (r (.GPR 23#5) t).toNat + 80 ≤ 2^64) :
    widthLoad (roundResult t base) (r (.GPR 23#5) t).toNat 8 = some 1 ∧
    widthLoad (roundResult t base) ((r (.GPR 23#5) t).toNat + 72) 4 =
      some ((r (.GPR 19#5) t).setWidth 32).toNat ∧
    (∀ offset bytes, offset + bytes ≤ 64 →
      widthLoad (roundResult t base) ((r (.GPR 23#5) t).toNat + 8 + offset) bytes =
        widthLoad t ((r (.GPR 23#5) t).toNat + 8 + offset) bytes) := by
  refine ⟨?_, ?_, ?_⟩
  · simp (config := {decide := true}) only
      [widthLoad, roundResult, ErrorTail.Tail.result, state_simp_rules,
       BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp (disch := failure_side) only [BoolCodec.read_mem_bytes_write_mem_bytes_same,
      show (1#64).toNat = 1 by decide]
  · simp (config := {decide := true}) only
      [widthLoad, roundResult, ErrorTail.Tail.result, state_simp_rules,
       BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp (disch := failure_side) only
      [write_pair32, BitVec.add_assoc, state_simp_rules,
       BoolCodec.read_mem_bytes_write_mem_bytes_same,
       BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]
  · intro offset bytes within
    simp (config := {decide := true}) only
      [widthLoad, roundResult, ErrorTail.Tail.result, state_simp_rules,
       BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp (disch := failure_side) only [state_simp_rules,
      BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]

/-- The optional-add failure executes both actual runtime copies and the native
status/tag stores. In particular neither scratch-only status nor a zero padding
word is an entry assumption. -/
theorem rounding_failure {s c t : ArmState} {base : BitVec 64}
    {length quotient : SszNative.NatOperand} {data : Ssz.Bytes}
    {reason : SszNative.NatArithmetic.Failure}
    (owned : Owned s length data) (current : Working s t length)
    (post : NatAdd.Post (roundEntry c base) t quotient (.small 1))
    (args : RoundArguments s (roundEntry c base) length quotient)
    (failure : (rounding s length quotient).result = .error reason)
    (code : JointCodeAt t base) (aligned : CheckSPAlignment s)
    (pc : read_pc t = base + 3416#64) :
    ∃ fuel final, run fuel t = final ∧
      Terminal s final base data (.error (.arithmetic reason)) ∧
      MemoryFrame (localWrites s) t final := by
  have stored := post.result
  rw [args.model, failure, args.output] at stored
  change SszNative.NatArithmetic.errorAt (widthLoad t)
    (r (.GPR 31#5) s + 144#64).toNat reason at stored
  have loaded : read_mem_bytes 4 (r (.GPR 31#5) t + 208#64) t = status reason := by
    simpa only [current.sp, BitVec.add_assoc, show 144#64 + 64#64 = 208#64 by decide]
      using error_status stored
  let a := ExpectedStage.Stage.rounding.result t base
  have first : run 2 t = a :=
    ExpectedStage.executes .rounding t base code.body current.error (current.aligned aligned) pc
  have aCurrent : Registers s a := registers (current.after_expected .rounding base)
  have aCode : JointCodeAt a base := by rw [← first]; exact code.run _
  have aPC : read_pc a = base + 3424#64 := by
    simp only [a, ExpectedStage.Stage.result, state_simp_rules, loaded,
      if_neg (status_ne_zero reason)]
  have aStatus : (r (.GPR 19#5) a).setWidth 32 = status reason := by
    cases reason <;>
      simp (config := {decide := true}) [a, ExpectedStage.Stage.result, state_simp_rules, loaded, status]
  have aObserve : widthLoad a = widthLoad t := by
    funext address bytes
    simp only [a, widthLoad, ExpectedStage.Stage.result, state_simp_rules]
  let b := Stages.CallPreparation.roundTemporary.result a base
  have second : run 3 a = b := Stages.prepare .roundTemporary a base aCode.body
    aCurrent.error (aCurrent.aligned aligned) aPC
  have bCurrent : Registers s b := aCurrent.prepare .roundTemporary base
  have bCode : JointCodeAt b base := by rw [← second]; exact aCode.run _
  have bPC : read_pc b = base + 3436#64 := by
    simp only [b, Stages.CallPreparation.result, Stages.CallPreparation.stop, state_simp_rules]
  have b0 : r (.GPR 0#5) b = r (.GPR 31#5) s + 64#64 := by
    simp (config := {decide := true}) [b, Stages.CallPreparation.result, state_simp_rules, aCurrent.sp]
  have b1 : r (.GPR 1#5) b = r (.GPR 31#5) s + 144#64 := by
    simp (config := {decide := true}) [b, Stages.CallPreparation.result, state_simp_rules, aCurrent.sp]
  have b2 : r (.GPR 2#5) b = 64#64 := by
    simp (config := {decide := true}) [b, Stages.CallPreparation.result, state_simp_rules]
  obtain ⟨destination, source, separate⟩ := stack_copy_space owned 64 144 64
    (by decide) (by decide) (by decide)
  obtain ⟨fuel1, u, copy1, copied1⟩ := memcpy_correct .roundTemporary b base
    (Or.inr (Or.inl rfl)) bCode bCurrent.error bPC
    (by simpa only [b0, b2, show (64#64).toNat = 64 by decide] using destination)
    (by simpa only [b1, b2, show (64#64).toNat = 64 by decide] using source)
    (by simpa only [b0, b1, b2, show (64#64).toNat = 64 by decide] using separate)
  have uCurrent := bCurrent.copy copied1
  have uCode : JointCodeAt u base := by rw [← copy1]; exact bCode.run _
  let p := Stages.CallPreparation.roundError.result u base
  have third : run 4 u = p := Stages.prepare .roundError u base uCode.body
    uCurrent.error (uCurrent.aligned aligned) copied1.returned
  have pCurrent : Registers s p := uCurrent.prepare .roundError base
  have pCode : JointCodeAt p base := by rw [← third]; exact uCode.run _
  have pPC : read_pc p = base + 3456#64 := by
    simp only [p, Stages.CallPreparation.result, Stages.CallPreparation.stop, state_simp_rules]
  have p0 : r (.GPR 0#5) p = r (.GPR 0#5) s + 8#64 := by
    simp (config := {decide := true}) [p, Stages.CallPreparation.result, state_simp_rules, uCurrent.output]
  have p1 : r (.GPR 1#5) p = r (.GPR 31#5) s + 64#64 := by
    simp (config := {decide := true}) [p, Stages.CallPreparation.result, state_simp_rules, uCurrent.sp]
  have p2 : r (.GPR 2#5) p = 64#64 := by
    simp (config := {decide := true}) [p, Stages.CallPreparation.result, state_simp_rules]
  obtain ⟨destination2, source2, separate2⟩ := output_copy_space owned 8 64 64
    (by decide) (by decide) (by decide)
  obtain ⟨fuel2, v, copy2, copied2⟩ := memcpy_correct .roundError p base
    (Or.inr (Or.inr (Or.inl rfl))) pCode pCurrent.error pPC
    (by simpa only [p0, p2, show (64#64).toNat = 64 by decide] using destination2)
    (by simpa only [p1, p2, show (64#64).toNat = 64 by decide] using source2)
    (by simpa only [p0, p1, p2, show (64#64).toNat = 64 by decide] using separate2)
  have vCurrent := pCurrent.copy copied2
  have vCode : JointCodeAt v base := by rw [← copy2]; exact pCode.run _
  have fourth : run 2 v = ErrorTail.Tail.round.result v base := ErrorTail.executes .round v base
    vCode.body vCurrent.error (vCurrent.aligned aligned) copied2.returned
  have tailCurrent := vCurrent.tail .round base
  have tailCode : JointCodeAt (ErrorTail.Tail.round.result v base) base := by
    rw [← fourth]; exact vCode.run _
  have fifth : run 3 (ErrorTail.Tail.round.result v base) = roundResult v base :=
    ErrorTail.executes .tag _ base tailCode.body tailCurrent.error (tailCurrent.aligned aligned)
      (by simp only [ErrorTail.Tail.result, ErrorTail.Tail.stop, ErrorTail.Tail.start, state_simp_rules])
  have finalCurrent := tailCurrent.tail .tag base
  have whole : run (2 + (3 + (fuel1 + (4 + (fuel2 + (2 + 3)))))) t = roundResult v base := by
    rw [run_plus, first, run_plus, second, run_plus, copy1, run_plus, third,
      run_plus, copy2, run_plus, fourth, fifth]
  have vStatus : (r (.GPR 19#5) v).setWidth 32 = status reason := by
    rw [copied2.registers 19#5 (by decide) (by decide)]
    simp (config := {decide := true}) only [p, Stages.CallPreparation.result, state_simp_rules]
    rw [copied1.registers 19#5 (by decide) (by decide)]
    simpa (config := {decide := true}) only
      [b, Stages.CallPreparation.result, state_simp_rules] using aStatus
  have outputBound := owned.outputBound
  have out8 : (r (.GPR 0#5) s + 8#64).toNat = (r (.GPR 0#5) s).toNat + 8 := by bv_omega
  have copied : ∀ offset bytes, offset + bytes ≤ 64 →
      widthLoad v ((r (.GPR 0#5) s).toNat + 8 + offset) bytes =
        widthLoad t ((r (.GPR 31#5) s + 144#64).toNat + offset) bytes := by
    intro offset bytes within
    have right := copied2.copied offset bytes
      (by simpa only [p2, show (64#64).toNat = 64 by decide] using within)
    have left := copied1.copied offset bytes
      (by simpa only [b2, show (64#64).toNat = 64 by decide] using within)
    simp only [p0, p1, out8, p, preparation_observe] at right
    simp only [b0, b1, b, preparation_observe, aObserve] at left
    exact right.trans left
  obtain ⟨tag, finalStatus, preserved⟩ := round_fields v base (by rw [vCurrent.output]; exact outputBound)
  rw [vCurrent.output] at tag finalStatus preserved
  rw [vStatus] at finalStatus
  have field : ∀ offset bytes, offset + bytes ≤ 64 →
      widthLoad (roundResult v base) ((r (.GPR 0#5) s).toNat + 8 + offset) bytes =
        widthLoad t ((r (.GPR 31#5) s + 144#64).toNat + offset) bytes := by
    intro offset bytes within
    exact (preserved offset bytes within).trans (copied offset bytes within)
  have finalStored : SszNative.NatArithmetic.errorAt (widthLoad (roundResult v base))
      ((r (.GPR 0#5) s).toNat + 8) reason := by
    obtain ⟨h0, h8, h16, h24, h32, h40, h48, h56, hs⟩ := stored
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Nat.add_zero] using (field 0 8 (by decide)).trans (by simpa using h0)
    · exact (field 8 8 (by decide)).trans h8
    · exact (field 16 8 (by decide)).trans h16
    · exact (field 24 8 (by decide)).trans h24
    · exact (field 32 8 (by decide)).trans h32
    · exact (field 40 8 (by decide)).trans h40
    · exact (field 48 8 (by decide)).trans h48
    · exact (field 56 8 (by decide)).trans h56
    · cases reason <;> simpa [status, Nat.add_assoc] using finalStatus
  have frame1 : MemoryFrame (localWrites s) t a := by
    apply frame_of_memory
    simp only [a, ExpectedStage.Stage.result, state_simp_rules, ArmState.mem_w_eq_mem]
  have frame2 : MemoryFrame (localWrites s) a b := frame_of_memory (preparation_memory _ _ _)
  have frame3 : MemoryFrame (localWrites s) b u :=
    (stack_copy_covered owned 64 64 (by decide)).frame
      (by simpa only [b0, b2, show (64#64).toNat = 64 by decide] using copied1.frame)
  have frame4 : MemoryFrame (localWrites s) u p := frame_of_memory (preparation_memory _ _ _)
  have frame5 : MemoryFrame (localWrites s) p v :=
    (output_copy_covered owned 8 64 (by decide) (by decide)).frame
      (by simpa only [p0, p2, show (64#64).toNat = 64 by decide] using copied2.frame)
  refine ⟨_, _, whole, ⟨?_, finalCurrent.error, finalCurrent.sp,
    finalCurrent.vectors, error_result finalStored tag⟩,
    ((((frame1.trans frame2).trans frame3).trans frame4).trans frame5).trans
      ((tail_frame owned vCurrent .round base).trans (tail_frame owned tailCurrent .tag base))⟩
  simp only [roundResult, ErrorTail.Tail.result, ErrorTail.Tail.stop, state_simp_rules]

end SszArm.BitVector.ArithmeticFailure
