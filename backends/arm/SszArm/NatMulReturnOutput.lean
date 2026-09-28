import SszArm.NatMulReturnFrame

namespace SszArm.NatMul

open BoolCodec
open UintCodec (widthLoad)
open UintCodec.Tail (write_pair_words)
open Delimited (MemoryFrame Returned)

def outputReturnOps : List Op :=
  [.p1296, .p1300, .p1304, .p1308, .p1312, .p1316, .p1320, .p1324,
   .p1328, .p1332, .p1336, .p1340]

def outputReturnBody (s : ArmState) (base : BitVec 64) : ArmState :=
  block base outputReturnOps s

def outputReturnMemory (s : ArmState) : ArmState :=
  NatFromU128.scratchStatus
    (write_mem_bytes 16 (r (.GPR 24#5) s) (r (.GPR 8#5) s ++ r (.GPR 20#5) s) s)
    (r (.GPR 31#5) s) (r (.GPR 24#5) s + 64#64) (r (.GPR 9#5) s) (r (.GPR 10#5) s)

theorem output_return_effect (s : ArmState) (base : BitVec 64)
    (space : ReturnSpace s (r (.GPR 24#5) s)) :
    outputReturnBody s base = w .PC (base + 348#64) (outputReturnMemory s) := by
  have stack := space.stack
  have output := space.output
  have separate := space.separate
  have reads := NatFromU128.scratchStatus_reads
    (write_mem_bytes 16 (r (.GPR 24#5) s) (r (.GPR 8#5) s ++ r (.GPR 20#5) s) s)
    (r (.GPR 31#5) s) (r (.GPR 24#5) s + 64#64)
    (r (.GPR 9#5) s) (r (.GPR 10#5) s) stack (by bv_omega) (by bv_omega)
  simp [NatFromU128.scratchStatus, BitVec.sub_eq_add_neg] at reads
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f <;>
      simp (config := {decide := true, instances := true})
        [outputReturnBody, outputReturnOps, block, Op.effect, put, next,
          outputReturnMemory, NatFromU128.scratchStatus, state_simp_rules,
          BitVec.add_assoc, BitVec.sub_eq_add_neg, NatFromU128.store_field_write,
          reads.1, reads.2]
    all_goals
      rename_i reg
      by_cases h9 : reg = 9#5
      · subst reg; simp (config := {decide := true}) [state_simp_rules]
      · by_cases h10 : reg = 10#5
        · subst reg; simp (config := {decide := true}) [state_simp_rules]
        · by_cases h31 : reg = 31#5
          · subst reg; simp (config := {decide := true}) [state_simp_rules]
          · simp (disch := simp_all) [state_simp_rules]
  · simp [outputReturnBody, outputReturnOps, block, Op.effect, put, next,
      outputReturnMemory, NatFromU128.scratchStatus, state_simp_rules]
  · apply Memory.mem_eq_iff_read_mem_bytes_eq.mp
    simp [outputReturnBody, outputReturnOps, block, Op.effect, put, next,
      outputReturnMemory, NatFromU128.scratchStatus, state_simp_rules,
      ArmState.mem_w_eq_mem, NatFromU128.store_field_write,
      BitVec.add_assoc, BitVec.sub_eq_add_neg]
    all_goals simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem output_return_body_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1296#64) : run 12 s = outputReturnBody s base := by
  apply block_run base outputReturnOps s code error aligned
  have hpc : r .PC s = base + 1296#64 := pc
  simp [outputReturnOps, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem output_return_body_registers (s : ArmState) (base : BitVec 64)
    (space : ReturnSpace s (r (.GPR 24#5) s)) (reg : BitVec 5) :
    r (.GPR reg) (outputReturnBody s base) = r (.GPR reg) s := by
  rw [output_return_effect s base space]
  simp [outputReturnMemory, NatFromU128.scratchStatus, state_simp_rules]

theorem output_return_body_frame (s : ArmState) (base : BitVec 64)
    (space : ReturnSpace s (r (.GPR 24#5) s)) :
    MemoryFrame (returnWrites s (r (.GPR 24#5) s)) s (outputReturnBody s base) := by
  have stack := space.stack
  have output := space.output
  have separate := space.separate
  intro a outside
  have pair := outside ((r (.GPR 24#5) s).toNat, 16) (by simp [returnWrites])
  have status := outside ((r (.GPR 24#5) s).toNat + 64, 4) (by simp [returnWrites])
  have spill := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [returnWrites])
  rw [output_return_effect s base space]
  simp (disch := natadd_return_side)
    [outputReturnMemory, NatFromU128.scratchStatus, ArmState.mem_w_eq_mem, write_mem_bytes_frame]

theorem output_return_body_image (s : ArmState) (base : BitVec 64)
    (space : ReturnSpace s (r (.GPR 24#5) s)) (operand : SszNative.NatOperand)
    (pointer : r (.GPR 20#5) s = operand.pointer)
    (payload : r (.GPR 8#5) s = operand.payload)
    (input : operand.At (widthLoad s))
    (protected : NatAdd.OperandOwned (returnWrites s (r (.GPR 24#5) s)) operand) :
    SszNative.NatArithmetic.AddResultAt (widthLoad (outputReturnBody s base))
      (r (.GPR 24#5) s).toNat (.ok operand) := by
  have stack := space.stack
  have output := space.output
  have separate := space.separate
  refine ⟨⟨?_, ?_, NatAdd.operand_at_preserved
    (output_return_body_frame s base space) operand input protected⟩, ?_⟩
  all_goals
    rw [output_return_effect s base space]
    simp only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat]
    simp only [outputReturnMemory, NatFromU128.scratchStatus, state_simp_rules]
    rw [write_pair_words _ _ _ _ (by omega)]
    natadd_return_reads
    all_goals simp only [pointer, payload]

def outputReturned (s : ArmState) (base : BitVec 64) : ArmState :=
  restored .return (outputReturnBody s base) base

theorem output_return_run (entry s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1296#64) (saved : Saved entry s)
    (space : ReturnSpace s (r (.GPR 24#5) s)) (operand : SszNative.NatOperand)
    (pointer : r (.GPR 20#5) s = operand.pointer)
    (payload : r (.GPR 8#5) s = operand.payload)
    (input : operand.At (widthLoad s))
    (protected : NatAdd.OperandOwned (returnWrites s (r (.GPR 24#5) s)) operand) :
    run 19 s = outputReturned s base ∧ Returned entry (outputReturned s base) ∧
      SszNative.NatArithmetic.AddResultAt (widthLoad (outputReturned s base))
        (r (.GPR 24#5) s).toNat (.ok operand) ∧
      MemoryFrame (returnWrites s (r (.GPR 24#5) s)) s (outputReturned s base) := by
  have bodyFrame := output_return_body_frame s base space
  have bodySaved := saved.return_frame space (return_frame_widen bodyFrame)
    (output_return_body_registers s base space 31#5)
    (output_return_body_registers s base space 29#5)
    (by intro reg; rw [output_return_effect s base space]
        simp [outputReturnMemory, NatFromU128.scratchStatus, state_simp_rules])
  have bodyError : read_err (outputReturnBody s base) = .None :=
    (block_error base outputReturnOps s).trans error
  refine ⟨?_, return_restored entry _ base bodySaved bodyError, ?_, ?_⟩
  · rw [show 19 = 12 + 7 by decide, run_plus, output_return_body_run s base code error aligned pc]
    exact restore_run .return _ base
      (by simpa only [outputReturnBody, CodeAt, block_program] using code) bodyError
      (block_aligned base outputReturnOps s aligned)
      (by rw [output_return_effect s base space]; simp [state_simp_rules, RestorePath.start])
  · have loads := Memory.mem_eq_iff_read_mem_bytes_eq.mp (restore_memory .return (outputReturnBody s base) base)
    have observed : widthLoad (outputReturned s base) = widthLoad (outputReturnBody s base) := by
      funext a n; simp only [outputReturned, widthLoad, loads]
    rw [observed]
    exact output_return_body_image s base space operand pointer payload input protected
  · intro a outside
    exact (congrFun (restore_memory .return (outputReturnBody s base) base) a).trans (bodyFrame a outside)

end SszArm.NatMul
