import SszArm.BitVectorScopeFailureMemory
import SszArm.BitVectorScopeCall
import SszArm.BitVectorObserve
import SszArm.BitVectorTerminal

namespace SszArm.BitVector

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

/-- Execute a rejected exact-size check from its actual helper return. The
expected Nat may be Small, empty Large, or arbitrarily high-zero-padded Large;
its limbs may have been allocated by either preceding arithmetic helper. -/
theorem scope_failure_executes {s c t : ArmState}
    {length expected : SszNative.NatOperand} {data : Ssz.Bytes}
    (base : BitVec 64) (owned : Owned s length data)
    (atCall : Working s c length)
    (post : NatExact.Post (scopeEntry c base) t expected)
    (rejected : SszNative.NatNarrow.runExact expected (BitVec.ofNat 64 data.size) = false)
    (limbs : NatDivision.OperandOwned (localWrites s) expected)
    (code : JointCodeAt t base) (aligned : CheckSPAlignment s)
    (pc : read_pc t = base + 5964#64) :
    ∃ fuel final, run fuel t = final ∧
      Terminal s final base data (.error (.scope expected data.size)) ∧
      MemoryFrame (localWrites s) t final := by
  have args := scope_arguments base owned atCall
  have entryCurrent : Working s (scopeEntry c base) length :=
    (atCall.after_preparation .scope base (Or.inr (Or.inl rfl))).after_call .scope base
  have current := entryCurrent.after_return post.returned
  have stored : SszNative.NatNarrow.ExactResultAt (widthLoad t)
      (r (.GPR 31#5) s + 144#64).toNat expected (BitVec.ofNat 64 data.size) := by
    simpa only [args.1, args.2.2] using post.result
  have rejectedObject := stored
  simp only [SszNative.NatNarrow.ExactResultAt, rejected, Bool.false_eq_true,
    ↓reduceIte] at rejectedObject
  obtain ⟨textPointer, textLength, expectedPair, secondPointer, secondValue,
    thirdPointer, thirdValue, status⟩ := rejectedObject
  have readStatus := read_of_observe_offset t (r (.GPR 31#5) s + 144#64)
    64 4 3#32 status
  have shifted : (r (.GPR 31#5) s + 144#64) + BitVec.ofNat 64 64 =
      r (.GPR 31#5) s + 208#64 := by bv_omega
  rw [shifted] at readStatus
  let staged := ExpectedStage.Stage.scope.result t base
  have stageRun : run 2 t = staged := ExpectedStage.executes .scope t base
    code.body current.error (current.aligned aligned) pc
  have stagedCurrent : Working s staged length := current.after_expected .scope base
  have stagedCode : JointCodeAt staged base := by rw [← stageRun]; exact code.run _
  have stagedPC : read_pc staged = base + 5972#64 := by
    simp (config := {decide := true})
      [staged, ExpectedStage.Stage.result, state_simp_rules, current.sp, readStatus]
  let prepared := Stages.CallPreparation.scopeError.result staged base
  have preparedRun : run 3 staged = prepared := Stages.prepare .scopeError staged base
    stagedCode.body stagedCurrent.error (stagedCurrent.aligned aligned) stagedPC
  have preparedCurrent : Working s prepared length :=
    ScopeFailure.prepared_working stagedCurrent base
  have preparedCode : JointCodeAt prepared base := by
    rw [← preparedRun]
    exact stagedCode.run _
  have preparedPC : read_pc prepared = base + 5984#64 := by
    simp only [prepared, Stages.CallPreparation.result, Stages.CallPreparation.stop,
      state_simp_rules, BitVec.ofNat_eq_ofNat]
  have destination : r (.GPR 0#5) prepared = r (.GPR 0#5) s + 8#64 := by
    simp (config := {decide := true})
      [prepared, Stages.CallPreparation.result, state_simp_rules, stagedCurrent.output]
  have source : r (.GPR 1#5) prepared = r (.GPR 31#5) s + 144#64 := by
    simp (config := {decide := true})
      [prepared, Stages.CallPreparation.result, state_simp_rules, stagedCurrent.sp]
  have count : r (.GPR 2#5) prepared = 72#64 := by
    simp (config := {decide := true})
      [prepared, Stages.CallPreparation.result, state_simp_rules]
  have copyBytes : (72#64).toNat = 72 := rfl
  have space := output_copy_space owned 8 144 72 (by decide) (by decide) (by decide)
  obtain ⟨copyFuel, copied, copyRun, copyPost⟩ := memcpy_correct .scopeError prepared base
    (Or.inr (Or.inr (Or.inr rfl))) preparedCode preparedCurrent.error preparedPC
    (by simpa only [destination, count, copyBytes] using space.1)
    (by simpa only [source, count, copyBytes] using space.2.1)
    (by simpa only [destination, source, count, copyBytes] using space.2.2)
  have copiedCurrent := preparedCurrent.after_memcpy .scopeError base copyPost
  have copiedCode : JointCodeAt copied base := by rw [← copyRun]; exact preparedCode.run _
  have copiedPC : read_pc copied = base + 5988#64 := by
    simpa only [CallSite.offset, BitVec.ofNat_eq_ofNat] using copyPost.returned
  let final := ErrorTail.Tail.tag.result copied base
  have tailRun : run 3 copied = final := ErrorTail.executes .tag copied base
    copiedCode.body copiedCurrent.error (copiedCurrent.aligned aligned) copiedPC
  have copyFrame : MemoryFrame (localWrites s) prepared copied := by
    apply (output_copy_covered owned 8 72 (by decide) (by decide)).frame
    simpa only [destination, count, copyBytes] using copyPost.frame
  have frame : MemoryFrame (localWrites s) t final :=
    ((expected_frame owned current .scope base).trans
      (preparation_frame .scopeError staged base (localWrites s))).trans
      (copyFrame.trans (ScopeFailure.tag_frame owned copiedCurrent.output base))
  have expectedAt : expected.At (widthLoad final) :=
    NatDivision.operand_at_preserved frame expected post.input.representation limbs
  have preparedObserve : widthLoad prepared = widthLoad t := by
    rw [show widthLoad prepared = widthLoad staged from
      preparation_observe .scopeError staged base]
    funext address bytes
    simp only [staged, widthLoad, ExpectedStage.Stage.result, state_simp_rules]
  have outBound := owned.outputBound
  have copiedBound : (r (.GPR 23#5) copied).toNat + 80 ≤ 2^64 := by
    rw [copiedCurrent.output]
    exact outBound
  have tag : widthLoad final (r (.GPR 0#5) s).toNat 8 = some 1 := by
    simpa only [copiedCurrent.output] using
      ScopeFailure.tag_value copied base (by omega)
  have destinationNat : (r (.GPR 0#5) s + 8#64).toNat =
      (r (.GPR 0#5) s).toNat + 8 := by bv_omega
  have copied72 : ∀ offset bytes, offset + bytes ≤ 72 →
      widthLoad final ((r (.GPR 0#5) s).toNat + 8 + offset) bytes =
        widthLoad t ((r (.GPR 31#5) s + 144#64).toNat + offset) bytes := by
    intro offset bytes within
    have kept := ScopeFailure.tag_copied copied base copiedBound offset bytes within
    rw [copiedCurrent.output] at kept
    have moved := copyPost.copied offset bytes (by simpa only [count, copyBytes] using within)
    rw [destination, source, destinationNat, preparedObserve] at moved
    exact kept.trans moved
  have actualSize : (BitVec.ofNat 64 data.size).toNat = data.size := by
    have sizeBound := (r (.GPR 3#5) s).isLt
    have sizeEq := owned.length
    bv_omega
  have observed := scope_error_of_copy t final
    (r (.GPR 31#5) s + 144#64).toNat (r (.GPR 0#5) s).toNat
    (r (.GPR 2#5) s).toNat expected (BitVec.ofNat 64 data.size) data
    actualSize rejected stored expectedAt tag (fun offset bytes within =>
      copied72 offset bytes (by omega))
  have whole : run (2 + (3 + (copyFuel + 3))) t = final := by
    rw [run_plus, stageRun, run_plus, preparedRun, run_plus, copyRun, tailRun]
  refine ⟨_, final, whole, ?_, frame⟩
  refine ⟨?_, ?_, ?_, ?_, observed⟩
  · simp only [final, ErrorTail.Tail.result, ErrorTail.Tail.stop,
      state_simp_rules, BitVec.ofNat_eq_ofNat]
  · simpa (config := {decide := true})
      [final, ErrorTail.Tail.result, state_simp_rules] using copiedCurrent.error
  · simpa (config := {decide := true})
      [final, ErrorTail.Tail.result, state_simp_rules] using copiedCurrent.sp
  · intro reg low high
    simpa (config := {decide := true})
      [final, ErrorTail.Tail.result, state_simp_rules] using copiedCurrent.vectors reg low high

end SszArm.BitVector
