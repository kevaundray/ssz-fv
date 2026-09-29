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

private def outputStatusMemory (s : ArmState) : ArmState :=
  NatFromU128.scratchStatus s (r (.GPR 31#5) s) (r (.GPR 24#5) s + 64#64)
    (r (.GPR 9#5) s) (r (.GPR 10#5) s)

private def outputStatusAddress (s : ArmState) : ArmState :=
  w .PC (read_pc s + 4#64) (w (.GPR 9#5) (r (.GPR 24#5) s) s)

private def outputStatusOffset (s : ArmState) : ArmState :=
  w .PC (read_pc s + 8#64) (w (.GPR 9#5) (r (.GPR 24#5) s + 64#64) s)

private def outputStatusSource (s : ArmState) : ArmState :=
  w .PC (read_pc s + 12#64)
    (w (.GPR 10#5) 0#64 (w (.GPR 9#5) (r (.GPR 24#5) s + 64#64) s))

private def outputStatusStore (s : ArmState) : ArmState :=
  w .PC (read_pc s + 16#64)
    (w (.GPR 10#5) 0#64 (w (.GPR 9#5) (r (.GPR 24#5) s + 64#64)
      (write_mem_bytes 4 (r (.GPR 24#5) s + 64#64) 0#32 s)))

private theorem output_status_address (s : ArmState) (base : BitVec 64) :
    Op.p1312.effect base s = outputStatusAddress s := by
  simp only [Op.effect, put, next, outputStatusAddress]
  arm_state_nf <;> simp

private theorem output_status_offset (s : ArmState) (base : BitVec 64) :
    Op.p1316.effect base (outputStatusAddress s) = outputStatusOffset s := by
  simp only [Op.effect, put, next, outputStatusAddress, outputStatusOffset]
  arm_state_nf <;> simp [BitVec.add_assoc]

private theorem output_status_source (s : ArmState) (base : BitVec 64) :
    Op.p1320.effect base (outputStatusOffset s) = outputStatusSource s := by
  simp only [Op.effect, put, next, outputStatusOffset, outputStatusSource]
  arm_state_nf <;> simp [BitVec.add_assoc]

private theorem output_status_store (s : ArmState) (base : BitVec 64) :
    Op.p1324.effect base (outputStatusSource s) = outputStatusStore s := by
  simp only [Op.effect, next, outputStatusSource, outputStatusStore]
  arm_state_nf <;> simp [BitVec.add_assoc]

private theorem output_status_enter (s : ArmState) (base : BitVec 64) :
    block base [.p1300, .p1304, .p1308] s = NatMulWord.pairEnter s := by
  have first : Op.effect base .p1300 = NatMulWord.Op.effect base .p12 := by funext t; rfl
  have second : Op.effect base .p1304 = NatMulWord.Op.effect base .p16 := by funext t; rfl
  have third : Op.effect base .p1308 = NatMulWord.Op.effect base .p20 := by funext t; rfl
  simp only [block, List.foldl_cons, List.foldl_nil, first, second, third,
    NatMulWord.pair_enter_first, NatMulWord.pair_enter_second, NatMulWord.pair_enter_last]

private theorem output_status_stores (s : ArmState) (base : BitVec 64) :
    block base [.p1312, .p1316, .p1320, .p1324] s = outputStatusStore s := by
  simp only [block, List.foldl_cons, List.foldl_nil, output_status_address,
    output_status_offset, output_status_source, output_status_store]

private theorem output_status_restore (s : ArmState) (base : BitVec 64) :
    block base [.p1328, .p1332, .p1336] s = NatMulWord.pairRestore s := by
  have first : Op.effect base .p1328 = NatMulWord.Op.effect base .p44 := by funext t; rfl
  have second : Op.effect base .p1332 = NatMulWord.Op.effect base .p48 := by funext t; rfl
  have third : Op.effect base .p1336 = NatMulWord.Op.effect base .p52 := by funext t; rfl
  simp only [block, List.foldl_cons, List.foldl_nil, first, second, third,
    NatMulWord.pair_restore_first, NatMulWord.pair_restore_second, NatMulWord.pair_restore_last]

private def outputStatusCheckpoint (s : ArmState) : ArmState :=
  w .PC (read_pc s + 28#64)
    (w (.GPR 10#5) 0#64 (w (.GPR 9#5) (r (.GPR 24#5) s + 64#64)
      (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64) (outputStatusMemory s))))

private theorem output_status_checkpoint (s : ArmState) :
    outputStatusStore (NatMulWord.pairEnter s) = outputStatusCheckpoint s := by
  simp only [outputStatusStore, NatMulWord.pairEnter, outputStatusCheckpoint,
    outputStatusMemory, NatFromU128.scratchStatus]
  arm_state_nf <;> simp [BitVec.add_assoc, BitVec.sub_eq_add_neg]

/-- Restore only the three touched registers over an arbitrary memory state.
The store tree never appears in this register-file proof. -/
private theorem output_restore_summary (m : ArmState) (pc address : BitVec 64)
    (read9 : read_mem_bytes 8 (r (.GPR 31#5) m - 16#64) m = r (.GPR 9#5) m)
    (read10 : read_mem_bytes 8 (r (.GPR 31#5) m - 16#64 + 8#64) m = r (.GPR 10#5) m) :
    NatMulWord.pairRestore
      (w .PC pc (w (.GPR 10#5) 0#64 (w (.GPR 9#5) address
        (w (.GPR 31#5) (r (.GPR 31#5) m - 16#64) m)))) =
      w .PC (pc + 12#64) m := by
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f <;> simp only [NatMulWord.pairRestore] <;> arm_state_nf <;>
      simp only [BitVec.sub_add_cancel, read9, read10]
    case FLAG flag =>
      have pcApart : StateField.FLAG flag ≠ .PC := by intro equal; cases equal
      have gprApart (reg : BitVec 5) : StateField.FLAG flag ≠ .GPR reg := by
        intro equal
        cases equal
      simp only [r_of_w_different pcApart,
        r_of_w_different (gprApart 31#5), r_of_w_different (gprApart 9#5),
        r_of_w_different (gprApart 10#5)]
    all_goals
      rename_i reg
      by_cases h9 : reg = 9#5
      · subst reg; simp [state_simp_rules]
      · by_cases h10 : reg = 10#5
        · subst reg; simp [state_simp_rules]
        · by_cases h31 : reg = 31#5
          · subst reg; simp [state_simp_rules]
          · simp (disch := simp_all) [state_simp_rules]
  · simp [NatMulWord.pairRestore, state_simp_rules]
  · apply Memory.mem_eq_iff_read_mem_bytes_eq.mp
    simp only [NatMulWord.pairRestore, ArmState.mem_w_eq_mem]

private theorem output_status_finish (s : ArmState)
    (space : ReturnSpace s (r (.GPR 24#5) s)) :
    NatMulWord.pairRestore (outputStatusCheckpoint s) =
      w .PC (read_pc s + 40#64) (outputStatusMemory s) := by
  have stack := space.stack
  have output := space.output
  have separate := space.separate
  have fields (f : StateField) : r f (outputStatusMemory s) = r f s := by
    simp only [outputStatusMemory, NatFromU128.scratchStatus, r_of_write_mem_bytes]
  have reads := NatFromU128.scratchStatus_reads s (r (.GPR 31#5) s)
    (r (.GPR 24#5) s + 64#64) (r (.GPR 9#5) s) (r (.GPR 10#5) s)
    stack (by bv_omega) (by bv_omega)
  have read9 : read_mem_bytes 8 (r (.GPR 31#5) (outputStatusMemory s) - 16#64)
      (outputStatusMemory s) = r (.GPR 9#5) (outputStatusMemory s) := by
    rw [fields, fields]
    exact reads.2
  have read10 : read_mem_bytes 8 (r (.GPR 31#5) (outputStatusMemory s) - 16#64 + 8#64)
      (outputStatusMemory s) = r (.GPR 10#5) (outputStatusMemory s) := by
    rw [fields, fields]
    have address : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by
      bv_omega
    rw [address]
    exact reads.1
  have finish := output_restore_summary (outputStatusMemory s)
    (read_pc s + 28#64) (r (.GPR 24#5) s + 64#64) read9 read10
  simpa only [outputStatusCheckpoint, fields, BitVec.add_assoc, BitVec.reduceAdd] using finish

private def outputStatusOps : List Op :=
  [.p1300, .p1304, .p1308] ++ [.p1312, .p1316, .p1320, .p1324] ++
    [.p1328, .p1332, .p1336] ++ [.p1340]

private theorem output_status_effect (s : ArmState) (base : BitVec 64)
    (space : ReturnSpace s (r (.GPR 24#5) s)) :
    block base outputStatusOps s = w .PC (base + 348#64) (outputStatusMemory s) := by
  have append (xs ys : List Op) (t : ArmState) :
      block base (xs ++ ys) t = block base ys (block base xs t) := by
    simp only [block, List.foldl_append]
  rw [outputStatusOps, append, append, append,
    output_status_enter, output_status_stores, output_status_checkpoint,
    output_status_restore, output_status_finish s space]
  simp only [block, List.foldl_cons, List.foldl_nil, Op.effect, state_simp_rules]

private theorem output_pair_effect (s : ArmState) (base : BitVec 64) :
    Op.p1296.effect base s =
      w .PC (read_pc s + 4#64)
        (write_mem_bytes 16 (r (.GPR 24#5) s) (r (.GPR 8#5) s ++ r (.GPR 20#5) s) s) :=
  NatMulWord.return_store_next s 16 (r (.GPR 24#5) s)
    (r (.GPR 8#5) s ++ r (.GPR 20#5) s)

theorem output_return_effect (s : ArmState) (base : BitVec 64)
    (space : ReturnSpace s (r (.GPR 24#5) s)) :
    outputReturnBody s base = w .PC (base + 348#64) (outputReturnMemory s) := by
  have fields (reg : BitVec 5) : r (.GPR reg) (Op.p1296.effect base s) = r (.GPR reg) s := by
    rw [output_pair_effect]
    exact (r_of_w_different (by intro h; cases h)).trans r_of_write_mem_bytes
  have owned : ReturnSpace (Op.p1296.effect base s) (r (.GPR 24#5) (Op.p1296.effect base s)) :=
    ⟨by simpa only [fields] using space.stack,
     by simpa only [fields] using space.savedBound,
     by simpa only [fields] using space.output,
     by simpa only [fields] using space.separate⟩
  have append (xs ys : List Op) (t : ArmState) :
      block base (xs ++ ys) t = block base ys (block base xs t) := by
    simp only [block, List.foldl_append]
  have split : outputReturnOps = [.p1296] ++ outputStatusOps := rfl
  rw [outputReturnBody, split, append]
  rw [show block base [.p1296] s = Op.p1296.effect base s by rfl]
  rw [output_status_effect _ base owned, output_pair_effect]
  simp only [outputStatusMemory, outputReturnMemory, NatFromU128.scratchStatus]
  arm_state_nf

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
    (protection : NatAdd.OperandOwned (returnWrites s (r (.GPR 24#5) s)) operand) :
    SszNative.NatArithmetic.AddResultAt (widthLoad (outputReturnBody s base))
      (r (.GPR 24#5) s).toNat (.ok operand) := by
  have stack := space.stack
  have output := space.output
  have separate := space.separate
  refine ⟨⟨?_, ?_, NatAdd.operand_at_preserved
    (output_return_body_frame s base space) operand input protection⟩, ?_⟩
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
    (protection : NatAdd.OperandOwned (returnWrites s (r (.GPR 24#5) s)) operand) :
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
    exact output_return_body_image s base space operand pointer payload input protection
  · intro a outside
    exact (congrFun (restore_memory .return (outputReturnBody s base) base) a).trans (bodyFrame a outside)

end SszArm.NatMul
