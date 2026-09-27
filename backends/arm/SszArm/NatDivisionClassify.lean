import SszArm.NatDivisionScanClassify
import SszArm.NatDivisionEntry
import SszArm.NatDivisionCalls

namespace SszArm.NatDivision

open Delimited (MemoryFrame Protected)
open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem ScanFrame.tight_memory {s t : ArmState} (frame : ScanFrame s t) :
    MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16)] s t := by
  intro a outside
  have h := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp)
  have lower : 16 ≤ (r (.GPR 31#5) s).toNat ∨ (r (.GPR 31#5) s).toNat < 16 := by omega
  apply frame.memory a
  simp only [Prod.fst, Prod.snd] at h
  omega

theorem ScanFrame.saved {original s t : ArmState}
    (frame : ScanFrame s t) (saved : Saved original s)
    (stack : 80 ≤ (r (.GPR 31#5) original).toNat) : Saved original t := by
  apply saved.preserve stack frame.tight_memory
  · right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    rw [saved.sp]
    simp only [Prod.fst, Prod.snd]
    right
    bv_omega
  · exact frame.sp
  · intro reg low high
    apply frame.registers
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    bv_omega
  · intro reg low high
    exact congrArg (BitVec.setWidth 64) (frame.vectors reg)

theorem ScanFrame.local_frame {original s t : ArmState}
    (frame : ScanFrame s t) (sp : r (.GPR 31#5) s = r (.GPR 31#5) original - 64#64)
    (stack : 80 ≤ (r (.GPR 31#5) original).toNat) :
    MemoryFrame (localWrites original) s t := by
  intro a outside
  have h := outside ((r (.GPR 31#5) original).toNat - 80, 80) (by simp [localWrites])
  apply frame.memory a
  simp only [Prod.fst, Prod.snd] at h
  rw [sp]
  bv_omega

/-- Initial physical ownership is converted to the existing scanner's exact
operand relation, not to a newly normalized or existentially replaced list. -/
theorem scan_operand {original s : ArmState} (operand : SszNative.NatOperand)
    (owned : Owned original operand)
    (sp : r (.GPR 31#5) s = r (.GPR 31#5) original - 64#64)
    (pointer : r (.GPR 1#5) s = operand.pointer)
    (payload : r (.GPR 2#5) s = operand.payload)
    (input : operand.At (widthLoad s)) :
    NatCompare.Operand s (r (.GPR 1#5) s) (r (.GPR 2#5) s) operand.words := by
  rw [pointer, payload]
  cases operand with
  | small word => exact Or.inl ⟨rfl, rfl⟩
  | large pointer words =>
    have positive := input.1
    have physical := input.2.2.1
    have count : words.length < 2^64 := by omega
    refine Or.inr ⟨?_, ?_, owned.large_source pointer words sp, large_words s pointer words input⟩
    · intro zero; simp [zero] at positive
    · exact Nat.mod_eq_of_lt count

structure Classified (original current : ArmState) (base : BitVec 64)
    (operand : SszNative.NatOperand) : Prop where
  program : current.program = original.program
  error : read_err current = .None
  aligned : CheckSPAlignment current
  saved : Saved original current
  out : r (.GPR 19#5) current = r (.GPR 0#5) original
  divisor : r (.GPR 20#5) current = r (.GPR 3#5) original
  arena : r (.GPR 21#5) current = r (.GPR 4#5) original
  pointer : r (.GPR 1#5) current = operand.pointer
  payload : r (.GPR 2#5) current = operand.payload
  frame : MemoryFrame (localWrites original) original current
  input : operand.At (widthLoad current)
  branch : if operand.pointer = 0#64 then read_pc current = base + 300#64
    else LargeClassified base operand.words current

/-- Actual entry execution includes every save and both significant-count
scans. No operand value-size or canonical-input restriction is introduced. -/
theorem classify_run (s : ArmState) (base : BitVec 64) (operand : SszNative.NatOperand)
    (owned : Owned s operand) (hc : CodeAt s base)
    (he : read_err s = .None) (ha : CheckSPAlignment s) (hp : read_pc s = base) :
    ∃ fuel t, run fuel s = t ∧ Classified s t base operand := by
  let u := block base prologueOps s
  have hu := prologue_run s base hc he ha hp
  have saved := prologue_saved s base owned.stackBound
  have args := prologue_arguments s base
  have upointer : r (.GPR 1#5) u = operand.pointer :=
    (args.1 1#5 (by simp)).trans owned.operandPointer
  have upayload : r (.GPR 2#5) u = operand.payload :=
    (args.1 2#5 (by simp)).trans owned.operandPayload
  have uc : CodeAt u base := by simpa only [u, CodeAt, block_program] using hc
  have ue : read_err u = .None := (block_error _ _ _).trans he
  have ua : CheckSPAlignment u := block_aligned _ _ _ ha
  have up : read_pc u = base + 32#64 := prologue_pc s base hp
  have ui := prologue_input s base operand owned
  have input := scan_operand operand owned saved.sp upointer upayload ui
  obtain ⟨fuel, t, ht, frame, branch⟩ := classify_operand u base operand.words uc ue ua up input
  have local := (prologue_local_frame s base owned.stackBound).trans
    (frame.local_frame saved.sp owned.stackBound)
  refine ⟨8 + fuel, t, ?_, ?_⟩
  · rw [run_plus, hu, ht]
  · refine ⟨frame.program.trans (block_program _ _ _), frame.error.trans ue,
      frame.aligned ua, frame.saved saved owned.stackBound,
      (frame.registers 19#5 (by decide)).trans args.2.1,
      (frame.registers 20#5 (by decide)).trans args.2.2.1,
      (frame.registers 21#5 (by decide)).trans args.2.2.2,
      (frame.registers 1#5 (by decide)).trans upointer,
      (frame.registers 2#5 (by decide)).trans upayload, local,
      operand_at_preserved (local_frame (outcome s operand) local) operand
        owned.operandAt owned.operandOwned, ?_⟩
    simpa only [upointer] using branch

end SszArm.NatDivision
