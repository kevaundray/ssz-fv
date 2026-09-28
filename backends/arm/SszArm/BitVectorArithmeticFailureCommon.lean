import SszArm.BitVectorDivide
import SszArm.BitVectorRoundCall
import SszArm.BitVectorTerminal
import SszArm.BitVectorObserve
import SszArm.BitVectorErrorExec
import SszArm.UintResultMemory

namespace SszArm.BitVector.ArithmeticFailure

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

macro "failure_side" : tactic => `(tactic| first | assumption | omega | bv_omega)

/-- The error paths no longer need X20's original length: roundError replaces
it by the actual private status padding, which must not be normalized. -/
structure Registers (s t : ArmState) : Prop where
  error : read_err t = .None
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  output : r (.GPR 23#5) t = r (.GPR 0#5) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64

theorem registers {s t : ArmState} {length : SszNative.NatOperand}
    (current : Working s t length) : Registers s t :=
  ⟨current.error, current.sp, current.output, current.vectors⟩

theorem Registers.aligned {s t : ArmState} (current : Registers s t)
    (aligned : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, current.sp] using aligned

theorem Registers.prepare {s t : ArmState} (current : Registers s t)
    (phase : Stages.CallPreparation) (base : BitVec 64) :
    Registers s (phase.result t base) := by
  cases phase <;> constructor
  all_goals first
    | simpa (config := {decide := true}) [Stages.CallPreparation.result, state_simp_rules]
        using current.error
    | simpa (config := {decide := true}) [Stages.CallPreparation.result, state_simp_rules]
        using current.sp
    | simpa (config := {decide := true}) [Stages.CallPreparation.result, state_simp_rules]
        using current.output
    | intro reg low high
      simpa (config := {decide := true}) [Stages.CallPreparation.result, state_simp_rules]
        using current.vectors reg low high

theorem preparation_memory (phase : Stages.CallPreparation) (t : ArmState) (base : BitVec 64) :
    (phase.result t base).mem = t.mem := by
  cases phase <;> simp only [Stages.CallPreparation.result, state_simp_rules, ArmState.mem_w_eq_mem]

theorem preparation_observe (phase : Stages.CallPreparation) (t : ArmState) (base : BitVec 64) :
    widthLoad (phase.result t base) = widthLoad t := by
  funext address bytes
  simp only [widthLoad, Memory.State.read_mem_bytes_eq_mem_read_bytes,
    preparation_memory]

theorem Registers.copy {s c t : ArmState} {site : CallSite} {base : BitVec 64}
    (current : Registers s c) (post : CopyPost site c t base) : Registers s t := by
  refine ⟨post.error, post.sp.trans current.sp,
    (post.registers 23#5 (by decide) (by decide)).trans current.output, ?_⟩
  intro reg low high
  exact (congrArg (fun value : BitVec 128 => value.setWidth 64)
    (post.vectors reg (by bv_omega))).trans (current.vectors reg low high)

theorem Registers.tail {s t : ArmState} (current : Registers s t)
    (phase : ErrorTail.Tail) (base : BitVec 64) : Registers s (phase.result t base) := by
  cases phase <;> constructor
  all_goals first
    | simpa (config := {decide := true}) [ErrorTail.Tail.result, state_simp_rules]
        using current.error
    | simpa (config := {decide := true}) [ErrorTail.Tail.result, state_simp_rules]
        using current.sp
    | simpa (config := {decide := true}) [ErrorTail.Tail.result, state_simp_rules]
        using current.output
    | intro reg low high
      simpa (config := {decide := true}) [ErrorTail.Tail.result, state_simp_rules]
        using current.vectors reg low high

/-- This is a memory identity for the actual paired W-register store; the
unobserved upper half is retained, rather than replaced by zero. -/
theorem write_pair32 (s : ArmState) (address : BitVec 64) (lo hi : BitVec 32)
    (physical : address.toNat + 8 ≤ 2^64) :
    write_mem_bytes 8 address (hi ++ lo) s =
      write_mem_bytes 4 (address + 4#64) hi (write_mem_bytes 4 address lo s) := by
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    simp only [state_simp_rules]
  · simp only [state_simp_rules]
  · apply Memory.mem_eq_iff_read_mem_bytes_eq.mp
    funext a
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes]
    by_cases before : a.toNat < address.toNat
    · rw [Memory.write_bytes_eq_of_le before physical,
        Memory.write_bytes_eq_of_le (by bv_omega) (by bv_omega),
        Memory.write_bytes_eq_of_le before (by omega)]
    · by_cases after : address.toNat + 8 ≤ a.toNat
      · rw [Memory.write_bytes_eq_of_ge after physical,
          Memory.write_bytes_eq_of_ge (by bv_omega) (by bv_omega),
          Memory.write_bytes_eq_of_ge (by omega) (by omega)]
      · rw [Memory.write_bytes_eq_extractLsByte (by omega) (by omega) physical]
        by_cases low : a.toNat < address.toNat + 4
        · rw [Memory.write_bytes_eq_of_le (by bv_omega) (by bv_omega),
            Memory.write_bytes_eq_extractLsByte (by omega) low (by omega)]
          simp only [BitVec.extractLsByte_def]
          exact BitVec.extractLsb'_append_eq_of_add_le (by bv_omega)
        · rw [Memory.write_bytes_eq_extractLsByte (by bv_omega) (by bv_omega) (by bv_omega)]
          simp only [BitVec.extractLsByte_def]
          rw [BitVec.extractLsb'_append_eq_of_le (by bv_omega)]
          congr 1
          bv_omega

def status (reason : SszNative.NatArithmetic.Failure) : BitVec 32 :=
  match reason with
  | .scratchExhausted => 32768#32
  | .badRepresentation => 32770#32

theorem status_ne_zero (reason : SszNative.NatArithmetic.Failure) : status reason ≠ 0 := by
  cases reason <;> decide

theorem error_status {t : ArmState} {pointer : BitVec 64}
    {reason : SszNative.NatArithmetic.Failure}
    (stored : SszNative.NatArithmetic.errorAt (widthLoad t) pointer.toNat reason) :
    read_mem_bytes 4 (pointer + 64#64) t = status reason := by
  apply read_of_observe_offset
  cases reason <;> exact stored.2.2.2.2.2.2.2.2

theorem error_result {t : ArmState} {out input : Nat} {data : Ssz.Bytes}
    {reason : SszNative.NatArithmetic.Failure}
    (stored : SszNative.NatArithmetic.errorAt (widthLoad t) (out + 8) reason)
    (tag : widthLoad t out 8 = some 1) :
    SszNative.BitVector.ResultAt (widthLoad t) out input data (.error (.arithmetic reason)) := by
  exact arithmetic_error_of_copy t t (out + 8) out reason stored tag
    (by intro offset bytes within; rfl)

theorem tail_frame {s t : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (current : Registers s t)
    (phase : ErrorTail.Tail) (base : BitVec 64) :
    MemoryFrame (localWrites s) t (phase.result t base) := by
  have output := owned.outputBound
  intro address outside
  have away := outside ((r (.GPR 0#5) s).toNat, 80) (by simp [localWrites])
  cases phase <;>
    simp (config := {decide := true}) only
      [ErrorTail.Tail.result, state_simp_rules, ArmState.mem_w_eq_mem, current.output]
  all_goals simp (disch := failure_side) only [BoolCodec.write_mem_bytes_frame]

end SszArm.BitVector.ArithmeticFailure
