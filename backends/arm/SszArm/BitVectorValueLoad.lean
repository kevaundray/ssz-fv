import SszArm.BitVectorValueState
import SszArm.BitVectorValueArithmetic

namespace SszArm.BitVector.ValueTail

open Block
open Delimited (MemoryFrame)

def loadResult (s : ArmState) (base : BitVec 64) : ArmState :=
  LoadStage.shiftRestore.result
    (LoadStage.shift.result
      (LoadStage.payload.result
        (LoadStage.someRestore.result (LoadStage.tag.result s base) base) base) base) base

/-- The Some discriminant is observed before the lowering spill. It selects
6612, so no instruction on the None continuation is executed. -/
theorem load_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 6592#64)
    (tag : read_mem_bytes 4 (r (.GPR 31#5) s + 144#64) s = 1#32) :
    run 15 s = loadResult s base := by
  have first := load_executes .tag s base code error aligned pc
  have second := load_executes .someRestore (LoadStage.tag.result s base) base
    (by simpa only [CodeAt, load_program] using code)
    (by simpa only [load_error] using error)
    (load_aligned _ _ _ aligned)
    (by simp [LoadStage.result, LoadStage.start, state_simp_rules, tag])
  have third := load_executes .payload
    (LoadStage.someRestore.result (LoadStage.tag.result s base) base) base
    (by simpa only [CodeAt, load_program] using code)
    (by simpa only [load_error] using error)
    (load_aligned _ _ _ (load_aligned _ _ _ aligned))
    (by simp [LoadStage.result, LoadStage.start, state_simp_rules])
  have fourth := load_executes .shift
    (LoadStage.payload.result (LoadStage.someRestore.result (LoadStage.tag.result s base) base) base) base
    (by simpa only [CodeAt, load_program] using code)
    (by simpa only [load_error] using error)
    (load_aligned _ _ _ (load_aligned _ _ _ (load_aligned _ _ _ aligned)))
    (by simp [LoadStage.result, LoadStage.start, state_simp_rules])
  have last := load_executes .shiftRestore
    (LoadStage.shift.result
      (LoadStage.payload.result (LoadStage.someRestore.result (LoadStage.tag.result s base) base) base) base) base
    (by simpa only [CodeAt, load_program] using code)
    (by simpa only [load_error] using error)
    (load_aligned _ _ _ (load_aligned _ _ _ (load_aligned _ _ _ (load_aligned _ _ _ aligned))))
    (by simp [LoadStage.result, LoadStage.start, state_simp_rules])
  change run 5 s = _ at first
  change run 3 _ = _ at second
  change run 3 _ = _ at third
  change run 2 _ = _ at fourth
  change run 2 _ = _ at last
  change run (5 + (3 + (3 + (2 + 2)))) s = _
  rw [run_plus, first, run_plus, second, run_plus, third, run_plus, fourth, last]
  rfl

@[simp] theorem loaded_pc (s : ArmState) (base : BitVec 64) :
    read_pc (loadResult s base) = base + 6664#64 := by
  simp [loadResult, LoadStage.result, state_simp_rules]

@[simp] theorem loaded_program (s : ArmState) (base : BitVec 64) :
    (loadResult s base).program = s.program := by simp [loadResult]

@[simp] theorem loaded_error (s : ArmState) (base : BitVec 64) :
    read_err (loadResult s base) = read_err s := by simp [loadResult]

@[simp] theorem loaded_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (loadResult s base) = r (.GPR 31#5) s := by
  simp [loadResult, LoadStage.result, state_simp_rules, BitVec.sub_add_cancel]

theorem loaded_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (r8 : reg ≠ 8#5) (r9 : reg ≠ 9#5) (r10 : reg ≠ 10#5)
    (r11 : reg ≠ 11#5) (rsp : reg ≠ 31#5) :
    r (.GPR reg) (loadResult s base) = r (.GPR reg) s := by
  simp only [loadResult, load_register _ _ _ _ r8 r9 r10 r11 rsp]

@[simp] theorem loaded_vector (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (loadResult s base) = r (.SFP reg) s := by simp [loadResult]

macro "value_side" : tactic => `(tactic| first | assumption | omega | bv_omega)

macro "value_reads" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [state_simp_rules, ArmState.mem_w_eq_mem, BitVec.add_assoc,
     BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.zero_add,
     BitVec.ofNat_add_ofNat, Nat.reduceAdd, BitVec.sub_add_cancel, BitVec.add_sub_cancel] <;>
    simp (config := {decide := true, instances := true}) (disch := value_side) only
      [BoolCodec.read_mem_bytes_write_mem_bytes_same, BoolCodec.read_mem_bytes_write_mem_bytes_disjoint])

theorem loaded_low (s : ArmState) (base : BitVec 64)
    (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat)
    (stackHigh : (r (.GPR 31#5) s).toNat + 176 ≤ 2^64) :
    r (.GPR 9#5) (loadResult s base) = read_mem_bytes 8 (r (.GPR 31#5) s + 160#64) s := by
  unfold loadResult
  simp only [LoadStage.result]
  value_reads

theorem loaded_high (s : ArmState) (base : BitVec 64)
    (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat)
    (stackHigh : (r (.GPR 31#5) s).toNat + 176 ≤ 2^64) :
    r (.GPR 8#5) (loadResult s base) = read_mem_bytes 8 (r (.GPR 31#5) s + 168#64) s := by
  unfold loadResult
  simp only [LoadStage.result]
  value_reads

theorem loaded_quotient (s : ArmState) (base : BitVec 64)
    (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat)
    (stackHigh : (r (.GPR 31#5) s).toNat + 176 ≤ 2^64) :
    r (.GPR 10#5) (loadResult s base) =
      quotientWord (read_mem_bytes 8 (r (.GPR 31#5) s + 160#64) s)
        (read_mem_bytes 8 (r (.GPR 31#5) s + 168#64) s) := by
  unfold loadResult quotientWord
  simp only [LoadStage.result]
  value_reads

theorem loaded_frame (s : ArmState) (base : BitVec 64)
    (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16)] s (loadResult s base) := by
  intro address outside
  have spill := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp)
  simp (config := {decide := true, instances := true}) only
    [loadResult, LoadStage.result, state_simp_rules, ArmState.mem_w_eq_mem, BitVec.sub_add_cancel]
  simp (disch := value_side) only [BoolCodec.write_mem_bytes_frame]
  simp only [ArmState.mem_w_eq_mem]
  exact BoolCodec.write_mem_bytes_frame s _ 8 _ address (by bv_omega) (by bv_omega)

end SszArm.BitVector.ValueTail
