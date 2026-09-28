import SszArm.MeasureUintClz
import SszArm.MeasureResultMemory

namespace SszArm.Measure.Uint

open UintCodec

def clzEnterOps : List CountOp := [.p2204, .p2208, .p2212, .p2216, .p2220, .p2224]
def clzExitOps : List CountOp := [.p2240, .p2244, .p2248, .p2252]

theorem clz_block (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 2204#64) (safe : 16 ≤ (r (.GPR 31#5) s).toNat) :
    ∃ t, run (10 + 3 * SszNative.Serialize.bitLength (r (.GPR 8#5) s).toNat) s = t ∧
      NatNarrow.Frame s t ∧ read_pc t = base + 2256#64 ∧
      r (.GPR 8#5) t = 64#64 - BitVec.ofNat 64
        (SszNative.Serialize.bitLength (r (.GPR 8#5) s).toNat) ∧
      r (.GPR 9#5) t = r (.GPR 9#5) s ∧ r (.GPR 10#5) t = r (.GPR 10#5) s := by
  let bits := SszNative.Serialize.bitLength (r (.GPR 8#5) s).toNat
  obtain ⟨bitsBound, after, before⟩ := bitLength_shift_facts (r (.GPR 8#5) s)
  let u := countBlock base clzEnterOps s
  have pc' : r .PC s = base + 2204#64 := pc
  have enterFollows : CountFollows base clzEnterOps s := by
    simp [clzEnterOps, CountFollows, CountOp.row, CountOp.effect, put, next,
      Emit.Dispatch.next, state_simp_rules, pc', BitVec.add_assoc]
  have enterRun : run 6 s = u := count_run base clzEnterOps s code error aligned enterFollows
  have enterProgram : u.program = s.program := by simp [u, countBlock, clzEnterOps]
  have enterError : read_err u = .None := by simp [u, countBlock, clzEnterOps, error]
  have enterAligned : CheckSPAlignment u := by
    simpa [u, countBlock, clzEnterOps, CountOp.effect, put, next, Emit.Dispatch.next,
      state_simp_rules, CheckSPAlignment] using
        BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s aligned)
  have enterPC : read_pc u = if bits = 0 then base + 2240#64 else base + 2228#64 := by
    by_cases zero : r (.GPR 8#5) s = 0#64
    · simp [u, bits, SszNative.Serialize.bitLength, zero, countBlock, clzEnterOps,
        CountOp.effect, put, next, Emit.Dispatch.next, state_simp_rules]
    · have nonzero : (r (.GPR 8#5) s).toNat ≠ 0 := by
        intro falseZero
        apply zero
        exact BitVec.eq_of_toNat_eq (by simpa using falseZero)
      simp [u, bits, SszNative.Serialize.bitLength, zero, nonzero, countBlock,
        clzEnterOps, CountOp.effect, put, next, Emit.Dispatch.next, state_simp_rules]
  have enterWord : r (.GPR 9#5) u = r (.GPR 8#5) s := by
    simp [u, countBlock, clzEnterOps, CountOp.effect, put, next, Emit.Dispatch.next,
      state_simp_rules]
  have enterCounter : r (.GPR 10#5) u = 64#64 := by
    simp [u, countBlock, clzEnterOps, CountOp.effect, put, next, Emit.Dispatch.next,
      state_simp_rules]
  obtain ⟨v, loopRun, loopFrame, loopPC, loopZero, loopCounter⟩ := clz_loop base bits u
    (code.congr enterProgram) enterError enterAligned enterPC
    (by simpa only [enterWord] using before) (by simpa only [enterWord] using after)
  have spillOffset : r (.GPR 31#5) s - 16#64 + 8#64 = r (.GPR 31#5) s - 8#64 := by bv_omega
  have loopMemory : v.mem = (Result.savedPair s 10#5).mem := by
    rw [loopFrame.memory]
    simp [u, countBlock, clzEnterOps, CountOp.effect, put, next, Emit.Dispatch.next,
      Result.savedPair, state_simp_rules, NatCompare.spill_mem_w, spillOffset]
    apply mem_write_mem_bytes_of_mem_eq
    simp [NatCompare.spill_mem_w]
  have loopRegs : ∀ reg : BitVec 5, reg ≠ 9#5 → reg ≠ 10#5 →
      r (.GPR reg) v = if reg = 31#5 then r (.GPR 31#5) s - 16#64 else r (.GPR reg) s := by
    intro reg nine ten
    rw [loopFrame.registers reg nine ten]
    simp [u, countBlock, clzEnterOps, CountOp.effect, put, next, Emit.Dispatch.next,
      state_simp_rules, nine, ten]
    by_cases stack : reg = 31#5
    · subst reg
      simp [state_simp_rules]
    · simp [stack, state_simp_rules]
  have loopStack : r (.GPR 31#5) v = r (.GPR 31#5) s - 16#64 := by
    simpa using loopRegs 31#5 (by decide) (by decide)
  have low : read_mem_bytes 8 (r (.GPR 31#5) v) v = r (.GPR 9#5) s := by
    rw [loopStack, (Memory.mem_eq_iff_read_mem_bytes_eq.mp loopMemory) 8]
    exact Result.savedPair_read_low s 10#5 safe
  have high : read_mem_bytes 8 (r (.GPR 31#5) v + 8#64) v = r (.GPR 10#5) s := by
    rw [loopStack, spillOffset, (Memory.mem_eq_iff_read_mem_bytes_eq.mp loopMemory) 8]
    exact Result.savedPair_read_high s 10#5 safe
  let t := countBlock base clzExitOps v
  have exitFollows : CountFollows base clzExitOps v := by
    have loopPC' : r .PC v = base + 2240#64 := loopPC
    simp [clzExitOps, CountFollows, CountOp.row, CountOp.effect, put, next,
      Emit.Dispatch.next, state_simp_rules, loopPC', BitVec.add_assoc]
  have exitRun : run 4 v = t := count_run base clzExitOps v
    (code.congr (loopFrame.program.trans enterProgram))
    (loopFrame.error.trans enterError) (loopFrame.aligned enterAligned) exitFollows
  have memory : t.mem = (Result.savedPair s 10#5).mem := by
    simpa [t, countBlock, clzExitOps, CountOp.effect, put, next, Emit.Dispatch.next,
      state_simp_rules] using loopMemory
  refine ⟨t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 10 + 3 * bits = 6 + 3 * bits + 4 by omega, run_plus, run_plus,
      enterRun, loopRun, exitRun]
  · constructor
    · simpa [t, countBlock, clzExitOps] using loopFrame.program.trans enterProgram
    · simpa [t, countBlock, clzExitOps] using loopFrame.error.trans
        (show read_err u = read_err s by simp [u, countBlock, clzEnterOps])
    · intro reg outside
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
      by_cases stack : reg = 31#5
      · subst reg
        simp [t, countBlock, clzExitOps, CountOp.effect, put, next, Emit.Dispatch.next,
          state_simp_rules, loopStack]
        bv_omega
      · simp [t, countBlock, clzExitOps, CountOp.effect, put, next, Emit.Dispatch.next,
          state_simp_rules, outside.1, outside.2.1, outside.2.2.1, stack,
          loopRegs reg outside.2.1 outside.2.2.1]
    · intro reg
      simpa [t, u, countBlock, clzExitOps, clzEnterOps, CountOp.effect, put, next,
        Emit.Dispatch.next, state_simp_rules] using loopFrame.vectors reg
    · intro address outside
      rw [memory]
      unfold Result.savedPair
      rw [BoolCodec.write_mem_bytes_frame _ _ 8 _ address (by bv_omega) (by bv_omega),
        BoolCodec.write_mem_bytes_frame _ _ 8 _ address (by bv_omega) (by bv_omega)]
  · have loopPC' : r .PC v = base + 2240#64 := loopPC
    simp [t, countBlock, clzExitOps, CountOp.effect, put, next, Emit.Dispatch.next,
      state_simp_rules, loopPC', BitVec.add_assoc]
  · simpa [t, countBlock, clzExitOps, CountOp.effect, put, next, Emit.Dispatch.next,
      state_simp_rules, enterCounter] using loopCounter
  · simp [t, countBlock, clzExitOps, CountOp.effect, put, next, Emit.Dispatch.next,
      state_simp_rules, low]
  · simp [t, countBlock, clzExitOps, CountOp.effect, put, next, Emit.Dispatch.next,
      state_simp_rules, high]

end SszArm.Measure.Uint
