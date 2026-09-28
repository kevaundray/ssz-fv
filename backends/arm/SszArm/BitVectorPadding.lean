import SszArm.BitVectorPaddingLower

namespace SszArm.BitVector.Padding

open Delimited (Span MemoryFrame)

/-- The native reason-setting instruction lies between the first two lowerings. -/
def reasonResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 6104#64) (w (.GPR 8#5) 15#64 s)

def result (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 8224#64)
    (Store.text.result
      (Store.first.result
        (Store.second.result
          (reasonResult (Store.third.result s base) base) base) base) base)

theorem reason_space (s : ArmState) (base : BitVec 64) (space : Space s) :
    Space (reasonResult s base) := by
  obtain ⟨stack, output, separate⟩ := space
  constructor
  · simpa [reasonResult, state_simp_rules] using stack
  · simpa [reasonResult, state_simp_rules] using output
  · simpa [reasonResult, state_simp_rules] using separate

private theorem pc_error (s : ArmState) (address : BitVec 64) :
    read_err (w .PC address s) = read_err s := by
  simp (config := {decide := true, instances := true}) [state_simp_rules]

private theorem reason_error (s : ArmState) (base : BitVec 64) :
    read_err (reasonResult s base) = read_err s := by
  simp (config := {decide := true, instances := true}) [reasonResult, state_simp_rules]

private theorem reason_aligned (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (reasonResult s base) := by
  simpa (config := {decide := true, instances := true})
    [reasonResult, CheckSPAlignment, state_simp_rules, bitvec_rules, minimal_theory] using aligned

/-- Actual row-by-row execution, with the count derived from the bounded cuts. -/
theorem executes (s : ArmState) (base : BitVec 64)
    (space : Space s) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 6052#64) :
    run 48 s = result s base := by
  have first := lower_run .third s base space code error aligned pc
  have reason := reason_run (Store.third.result s base) base
    (by simpa only [CodeAt, result_program] using code)
    (by simpa only [result_error] using error)
    (by simp [Store.stop])
  have second := lower_run .second (reasonResult (Store.third.result s base) base) base
    (reason_space _ _ (result_space _ _ _ space))
    (by simpa only [CodeAt, reasonResult, state_simp_rules, result_program] using code)
    (by simpa only [reason_error, result_error] using error)
    (reason_aligned _ _ (result_aligned _ _ _ aligned))
    (by simp [reasonResult, Store.start, state_simp_rules])
  have third := lower_run .first
    (Store.second.result (reasonResult (Store.third.result s base) base) base) base
    (result_space _ _ _ (reason_space _ _ (result_space _ _ _ space)))
    (by simpa only [CodeAt, result_program, reasonResult, state_simp_rules] using code)
    (by simpa only [result_error, reason_error] using error)
    (result_aligned _ _ _ (reason_aligned _ _ (result_aligned _ _ _ aligned)))
    (by simp [Store.start, Store.stop])
  have fourth := lower_run .text
    (Store.first.result
      (Store.second.result (reasonResult (Store.third.result s base) base) base) base) base
    (result_space _ _ _ (result_space _ _ _ (reason_space _ _ (result_space _ _ _ space))))
    (by simpa only [CodeAt, result_program, reasonResult, state_simp_rules] using code)
    (by simpa only [result_error, reason_error] using error)
    (result_aligned _ _ _ (result_aligned _ _ _
      (reason_aligned _ _ (result_aligned _ _ _ aligned))))
    (by simp [Store.start, Store.stop])
  have branch := branch_run
    (Store.text.result (Store.first.result
      (Store.second.result (reasonResult (Store.third.result s base) base) base) base) base) base
    (by simpa only [CodeAt, result_program, reasonResult, state_simp_rules] using code)
    (by simpa only [result_error, reason_error] using error)
    (by simp [Store.stop])
  change run 1 (Store.third.result s base) = reasonResult (Store.third.result s base) base at reason
  change run 12 s = _ at first
  change run 12 (reasonResult (Store.third.result s base) base) = _ at second
  change run 12 (Store.second.result (reasonResult (Store.third.result s base) base) base) = _ at third
  change run 10 (Store.first.result
    (Store.second.result (reasonResult (Store.third.result s base) base) base) base) = _ at fourth
  change run (12 + (1 + (12 + (12 + (10 + 1))))) s = _
  rw [run_plus, first, run_plus, reason, run_plus, second, run_plus, third,
    run_plus, fourth, branch]
  rfl

@[simp] theorem final_pc (s : ArmState) (base : BitVec 64) :
    read_pc (result s base) = base + 8224#64 := by
  simp [result, state_simp_rules]

@[simp] theorem final_reason (s : ArmState) (base : BitVec 64) :
    r (.GPR 8#5) (result s base) = 15#64 := by
  simp [result, result_register, reasonResult, state_simp_rules]

theorem final_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (kept : reg ≠ 8#5) : r (.GPR reg) (result s base) = r (.GPR reg) s := by
  simp [result, result_register, reasonResult, state_simp_rules, kept]

@[simp] theorem final_program (s : ArmState) (base : BitVec 64) :
    (result s base).program = s.program := by
  simp [result, reasonResult, state_simp_rules]

@[simp] theorem final_error (s : ArmState) (base : BitVec 64) :
    read_err (result s base) = read_err s := by
  simp only [result, pc_error, result_error, reason_error]

@[simp] theorem final_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (result s base) = r (.SFP reg) s := by
  simp [result, reasonResult, state_simp_rules]

def writes (s : ArmState) : List Span :=
  [((r (.GPR 23#5) s).toNat, 80), ((r (.GPR 31#5) s).toNat - 16, 16)]

macro "padding_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [result, reasonResult, Store.result, Store.image, Store.zeroImage,
     Store.displacement, NatExact.spillTwo, reduceCtorEq, ↓reduceIte,
     state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
     BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat, Nat.reduceAdd,
     BitVec.add_zero, BitVec.zero_add, BitVec.sub_add_cancel])

theorem final_frame (s : ArmState) (base : BitVec 64) (space : Space s) :
    MemoryFrame (writes s) s (result s base) := by
  obtain ⟨stack, output, separate⟩ := space
  intro address outside
  have out := outside ((r (.GPR 23#5) s).toNat, 80) (by simp [writes])
  have spill := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [writes])
  padding_expand
  simp (disch := padding_side) [BoolCodec.write_mem_bytes_frame, ArmState.mem_w_eq_mem]

end SszArm.BitVector.Padding
