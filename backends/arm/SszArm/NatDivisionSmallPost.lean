import SszArm.NatDivisionSerialize
import SszArm.NatDivisionPost
import SszArm.NatDivisionBodyMemory

namespace SszArm.NatDivision

open Delimited (MemoryFrame)
open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem output_local_frame {original s t : ArmState} {operand : SszNative.NatOperand}
    (owned : Owned original operand) (saved : Saved original s)
    (out : r (.GPR 19#5) s = r (.GPR 0#5) original)
    (frame : MemoryFrame (returnWrites s) s t) :
    MemoryFrame (localWrites original) s t := by
  apply frame_cover frame
  intro span member
  simp only [returnWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨((r (.GPR 0#5) original).toNat, 68),
      by simp [localWrites], by simp [out], by simp [out]⟩
  · refine ⟨((r (.GPR 31#5) original).toNat - 80, 80), by simp [localWrites], ?_, ?_⟩
    all_goals
      have stack := owned.stackBound
      simp only [Prod.fst, Prod.snd]
      rw [saved.sp]
      bv_omega

theorem small_head_registers (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (h9 : reg ≠ 9#5) (h10 : reg ≠ 10#5) :
    r (.GPR reg) (block base smallHeadOps s) = r (.GPR reg) s := by
  simp [block, smallHeadOps, Op.effect, put, next, state_simp_rules, h9, h10]

theorem small_head_saved (original s : ArmState) (base : BitVec 64)
    (saved : Saved original s) : Saved original (block base smallHeadOps s) := by
  have sp := small_head_registers s base 31#5 (by decide) (by decide)
  refine ⟨sp.trans saved.sp, ?_, ?_, ?_⟩
  · intro reg offset member
    rw [sp]
    have memory := Memory.mem_eq_iff_read_mem_bytes_eq.mp (small_head_data s base).2.2.2
    rw [memory]
    exact saved.words reg offset member
  · intro reg low high
    exact (small_head_registers s base reg (by bv_omega) (by bv_omega)).trans (saved.high reg low high)
  · intro reg low high
    simpa [block, smallHeadOps, Op.effect, put, next, state_simp_rules] using saved.vectors reg low high

/-- A zero high quotient word takes the allocation-free tail. The theorem
executes all 27 instructions from that branch through the original caller RET. -/
theorem small_result_post (original s : ArmState) (base : BitVec 64)
    (operand : SszNative.NatOperand) (remainder : BitVec 64)
    (owned : Owned original operand) (saved : Saved original s)
    (out : r (.GPR 19#5) s = r (.GPR 0#5) original)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 644#64)
    (source : outcome original operand = SszNative.NatArithmetic.unchanged
      (arenaOf original).used (.ok (.small (r (.GPR 0#5) s), remainder)))
    (rem : r (.GPR 22#5) s - r (.GPR 0#5) s * r (.GPR 20#5) s = remainder)
    (before : MemoryFrame (localWrites original) original s) :
    Post original (run 27 s) operand := by
  let h := block base smallHeadOps s
  have head := small_head_data s base
  have headSP := small_head_registers s base 31#5 (by decide) (by decide)
  have headOut := (small_head_registers s base 19#5 (by decide) (by decide)).trans out
  have headSaved := small_head_saved original s base saved
  have headCode : CodeAt h base := by simpa only [h, CodeAt, block_program] using hc
  have headError : read_err h = .None := (block_error _ _ _).trans he
  have headAlign : CheckSPAlignment h := block_aligned _ _ _ ha
  have headFrame : MemoryFrame (localWrites original) s h := by
    intro a _
    exact congrArg (fun memory => memory a) head.2.2.2
  have space : ReturnSpace h := owned.return_space headSaved.sp headOut
  let t := block base fastOutputOps h
  have args := fast_output_arguments h base space
  have savedAfter := fast_output_saved original h base headSaved owned.stackBound space
  have outAfter := args.2.2.2.2.1.trans headOut
  have outputFrame := output_local_frame owned headSaved headOut (fast_output_frame h base space)
  have completeFrame := (before.trans headFrame).trans outputFrame
  have ready : ReturnReady t (outcome original operand).result := by
    rw [source]
    apply fast_output_ready h base space (.small (r (.GPR 0#5) s)) remainder
    · exact head.2.1
    · exact head.2.2.1
    · simpa only [h, small_head_registers s base 22#5 (by decide) (by decide),
        small_head_registers s base 0#5 (by decide) (by decide),
        small_head_registers s base 20#5 (by decide) (by decide)] using rem
    · trivial
    · trivial
  have written : WrittenAt (widthLoad t) (outcome original operand) := by
    rw [source]
    intro reservation impossible
    cases impossible
  have cursor : (read_mem_bytes 8 (r (.GPR 4#5) original + 16#64) t).toNat =
      (outcome original operand).used := by
    have physical := owned.arenaBound
    have address : (r (.GPR 4#5) original + 16#64).toNat =
        (r (.GPR 4#5) original).toNat + 16 := by bv_omega
    rw [completeFrame.read _ 8 (by rw [address]; omega)]
    · rw [source]
      rfl
    · rw [address]
      exact owned.arenaLocal.subspan 16 8 (by decide)
  have code : CodeAt t base := by simpa only [t, CodeAt, block_program] using headCode
  have error : read_err t = .None := (block_error _ _ _).trans headError
  have aligned : CheckSPAlignment t := block_aligned _ _ _ headAlign
  rw [show 27 = 3 + 11 + 13 by decide, run_plus, run_plus,
    small_head_run s base hc he ha hp, fast_output_run h base headCode headError headAlign head.1]
  exact finish_post original t base operand owned savedAfter outAfter code error aligned args.1
    ready written cursor (local_frame (outcome original operand) completeFrame)

end SszArm.NatDivision
