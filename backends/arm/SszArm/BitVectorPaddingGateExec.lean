import SszArm.BitVectorPaddingCorrect
import SszArm.BitVectorTailExec
import SszArm.BitVectorTailGate
import SszArm.BitVectorStageState
import SszArm.DelimitedInput
import SszArm.DelimitedResults

namespace SszArm.BitVector.PaddingGate

open TailCheck
open Delimited (MemoryFrame)
open UintCodec (widthLoad)

def prepared (c : ArmState) (base : BitVec 64) := Stage.prepare.result c base
def loaded (c : ArmState) (base : BitVec 64) := Stage.byte.result (prepared c base) base
def restored (c : ArmState) (base : BitVec 64) := Stage.restore.result (loaded c base) base
def checked (c : ArmState) (base : BitVec 64) := Stage.test.result (restored c base) base

@[simp] theorem stage_program (stage : Stage) (c : ArmState) (base : BitVec 64) :
    (stage.result c base).program = c.program := by
  cases stage <;> simp [Stage.result, state_simp_rules]

@[simp] theorem stage_error (stage : Stage) (c : ArmState) (base : BitVec 64) :
    read_err (stage.result c base) = read_err c := by
  cases stage <;> simp (config := {decide := true}) [Stage.result, state_simp_rules]

theorem stage_aligned (stage : Stage) (c : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment c) : CheckSPAlignment (stage.result c base) := by
  have stack := BoolCodec.stack_aligned c aligned
  change Aligned (r (.GPR 31#5) c) 4 at stack
  cases stage <;>
    simp (config := {decide := true, instances := true}) only
      [Stage.result, CheckSPAlignment, state_simp_rules, bitvec_rules, minimal_theory,
       BoolCodec.aligned_sub16 _ stack, BoolCodec.aligned_add16 _ stack, stack]

theorem checked_run (c : ArmState) (base : BitVec 64) (code : CodeAt c base)
    (error : read_err c = .None) (aligned : CheckSPAlignment c)
    (pc : read_pc c = base + 6008#64) : run 11 c = checked c base := by
  have first := TailCheck.executes .prepare c base code error aligned pc
  have second := TailCheck.executes .byte (prepared c base) base
    (by simpa only [CodeAt, prepared, stage_program] using code)
    (by simpa only [prepared, stage_error] using error)
    (stage_aligned .prepare c base aligned)
    (by simp [prepared, Stage.result, Stage.start, state_simp_rules])
  have third := TailCheck.executes .restore (loaded c base) base
    (by simpa only [CodeAt, loaded, prepared, stage_program] using code)
    (by simpa only [loaded, prepared, stage_error] using error)
    (stage_aligned .byte _ _ (stage_aligned .prepare _ _ aligned))
    (by simp [loaded, Stage.result, Stage.start, state_simp_rules])
  have fourth := TailCheck.executes .test (restored c base) base
    (by simpa only [CodeAt, restored, loaded, prepared, stage_program] using code)
    (by simpa only [restored, loaded, prepared, stage_error] using error)
    (stage_aligned .restore _ _ (stage_aligned .byte _ _ (stage_aligned .prepare _ _ aligned)))
    (by simp [restored, Stage.result, Stage.start, state_simp_rules])
  change run 4 c = prepared c base at first
  change run 3 (prepared c base) = loaded c base at second
  change run 2 (loaded c base) = restored c base at third
  change run 2 (restored c base) = checked c base at fourth
  change run (4 + (3 + (2 + 2))) c = _
  rw [run_plus, first, run_plus, second, run_plus, third, fourth]

@[simp] theorem checked_program (c : ArmState) (base : BitVec 64) :
    (checked c base).program = c.program := by
  simp only [checked, restored, loaded, prepared, stage_program]

@[simp] theorem checked_error (c : ArmState) (base : BitVec 64) :
    read_err (checked c base) = read_err c := by
  simp only [checked, restored, loaded, prepared, stage_error]

theorem checked_register (c : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (h8 : reg ≠ 8#5) (h9 : reg ≠ 9#5) :
    r (.GPR reg) (checked c base) = r (.GPR reg) c := by
  by_cases stack : reg = 31#5
  · subst reg
    simp (config := {decide := true, instances := true})
      [checked, restored, loaded, prepared, Stage.result, state_simp_rules, BitVec.sub_add_cancel]
  · simp (config := {decide := true, instances := true})
      [checked, restored, loaded, prepared, Stage.result, state_simp_rules, h8, h9, stack]

@[simp] theorem checked_vector (c : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (checked c base) = r (.SFP reg) c := by
  simp (config := {decide := true, instances := true})
    [checked, restored, loaded, prepared, Stage.result, state_simp_rules]

theorem counted_of_preserved {s c t : ArmState} {length : SszNative.NatOperand}
    {remainder : BitVec 64} (current : Counted s c length remainder)
    (error : read_err t = read_err c)
    (regs : ∀ reg : BitVec 5, reg ≠ 8#5 → reg ≠ 9#5 → r (.GPR reg) t = r (.GPR reg) c)
    (vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) c) :
    Counted s t length remainder := by
  refine ⟨⟨error.trans current.error, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (regs 31#5 (by decide) (by decide)).trans current.sp
  · exact (regs 23#5 (by decide) (by decide)).trans current.output
  · exact (regs 24#5 (by decide) (by decide)).trans current.input
  · exact (regs 20#5 (by decide) (by decide)).trans current.size
  · exact (regs 21#5 (by decide) (by decide)).trans current.pointer
  · exact (regs 22#5 (by decide) (by decide)).trans current.payload
  · intro reg low high
    rw [vectors]
    exact current.vectors reg low high
  · exact (regs 25#5 (by decide) (by decide)).trans current.remainderValue

theorem checked_counted {s c : ArmState} {length : SszNative.NatOperand}
    {remainder : BitVec 64} (current : Counted s c length remainder) (base : BitVec 64) :
    Counted s (checked c base) length remainder :=
  counted_of_preserved current (checked_error c base) (checked_register c base) (checked_vector c base)

theorem prepared_frame {s c : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (sp : r (.GPR 31#5) c = r (.GPR 31#5) s)
    (base : BitVec 64) : MemoryFrame (localWrites s) c (prepared c base) := by
  have low := owned.stackLow
  intro address outside
  have stack := outside ((r (.GPR 31#5) s).toNat - 80, 352) (by simp [localWrites])
  simp only [prepared, Stage.result, ArmState.mem_w_eq_mem]
  apply BoolCodec.write_mem_bytes_frame <;> rw [sp] <;> bv_omega

theorem checked_frame {s c : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    {remainder : BitVec 64} (owned : Owned s length data) (current : Counted s c length remainder)
    (base : BitVec 64) : MemoryFrame (localWrites s) c (checked c base) := by
  have frame := prepared_frame owned current.sp base
  simpa only [MemoryFrame, checked, restored, loaded, Stage.result,
    ArmState.mem_w_eq_mem] using frame

theorem local_input_owned {s : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) :
    Delimited.Protected (localWrites s) (r (.GPR 2#5) s).toNat data.size :=
  (local_covered s (outcome s length data)).protected owned.inputOwned

theorem bytes_after_frame {s c t : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (frame : MemoryFrame (localWrites s) c t)
    (bytes : SszNative.ByteView.BytesAt (widthLoad c) (r (.GPR 2#5) s).toNat data) :
    SszNative.ByteView.BytesAt (widthLoad t) (r (.GPR 2#5) s).toNat data :=
  frame.bytes _ data owned.inputBound (local_input_owned owned) bytes

end SszArm.BitVector.PaddingGate
