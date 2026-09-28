import SszArm.MeasureUintValueFrame
import SszArm.NatCompareOrder

namespace SszArm.Measure.Uint

open SszNative.Limbs

def valueGuardOps : List ValueOp := [.p368]
def valueTailOps : List ValueOp := [.p404, .p408, .p412]

def valueRoundResult (s : ArmState) (base limb : BitVec 64) : ArmState :=
  valueBlock base valueTailOps
    (valueLoadResult (valueBlock base valueGuardOps s) base limb)

theorem value_scan_round (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 368#64)
    (pointerReg : r (.GPR 9#5) s = pointer - 8#64)
    (bound : n < words.length) (index : r (.GPR 8#5) s = BitVec.ofNat 64 (n + 1))
    (source : NatCompare.Source s pointer words) (memory : NatCompare.Words s pointer words) :
    let t := valueRoundResult s base (words[n]?.getD 0#64)
    run 12 s = t ∧ NatNarrow.Frame s t ∧
      r (.GPR 9#5) t = pointer - 8#64 ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 n ∧
      r (.GPR 10#5) t = BitVec.ofNat 64 (n + 1) ∧
      r (.GPR 11#5) t = words[n]?.getD 0#64 ∧
      read_pc t = base + BitVec.ofNat 64
        (if words[n]?.getD 0#64 = 0#64 then 368 else 416) := by
  have lengthBound : words.length < 2^64 := by have := source.2.1; omega
  have nonzero : BitVec.ofNat 64 (n + 1) ≠ 0#64 := by bv_omega
  let u := valueBlock base valueGuardOps s
  have pc' : r .PC s = base + 368#64 := pc
  have follows : ValueFollows base valueGuardOps s := by
    simp [valueGuardOps, ValueFollows, ValueOp.row, pc]
  have executed : run 1 s = u := value_run base valueGuardOps s code error aligned follows
  have frame : NatNarrow.Frame s u := value_pure_frame base _ s (by decide)
  have nextPC : read_pc u = base + 372#64 := by
    simp [u, valueGuardOps, valueBlock, ValueOp.effect, state_simp_rules, index, nonzero]
  have nextIndex : r (.GPR 8#5) u = BitVec.ofNat 64 (n + 1) := by
    simpa [u, valueGuardOps, valueBlock, ValueOp.effect, state_simp_rules] using index
  have nextPointer : r (.GPR 9#5) u = pointer - 8#64 := by
    simpa [u, valueGuardOps, valueBlock, ValueOp.effect, state_simp_rules] using pointerReg
  have nextSource := frame.source pointer words source
  have nextMemory := frame.words pointer words source memory
  have loaded : read_mem_bytes 8 (r (.GPR 9#5) u + (r (.GPR 8#5) u <<< 3))
      (NatCompare.saved u 10#5) = words[n]?.getD 0#64 := by
    rw [nextIndex, nextPointer]
    have address : pointer - 8#64 + (BitVec.ofNat 64 (n + 1) <<< 3) =
        pointer + (BitVec.ofNat 64 n <<< 3) := by
      simp only [BitVec.ofNat_add]
      bv_omega
    rw [address]
    exact NatCompare.limb_load u pointer words n 10#5 bound nextSource nextMemory
  let v := valueLoadResult u base (words[n]?.getD 0#64)
  have loadedRun : run 8 u = v := value_load_run u base _ (code.congr frame.program)
    (frame.error.trans error) (frame.aligned aligned) nextPC nextSource.1 loaded
  have loadedFrame : NatNarrow.Frame s v := frame.trans (value_load_frame u base _ nextSource.1)
  have tailFollows : ValueFollows base valueTailOps v := by
    simp [v, valueTailOps, valueLoadResult, ValueFollows, ValueOp.row, ValueOp.effect,
      put, next, Emit.Dispatch.next, state_simp_rules, BitVec.add_assoc]
  have tailRun : run 3 v = valueBlock base valueTailOps v := value_run base valueTailOps v
    (code.congr loadedFrame.program) (loadedFrame.error.trans error)
    (loadedFrame.aligned aligned) tailFollows
  refine ⟨?_, loadedFrame.trans (value_pure_frame base _ v (by decide)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 12 = 1 + 8 + 3 by decide, run_plus, run_plus, executed, loadedRun, tailRun]
    rfl
  all_goals simp [valueRoundResult, valueTailOps, valueLoadResult, valueGuardOps,
    valueBlock, ValueOp.effect, put, next, Emit.Dispatch.next, NatCompare.saved,
    state_simp_rules, index, pointerReg, apply_ite, BitVec.ofNat_add]
  all_goals bv_omega

/-- Descending through the actual value load loop retains arbitrary zero
padding. Empty and all-zero arrays leave at the genuine zero-width block. -/
theorem value_scan (base pointer : BitVec 64) (words : List (BitVec 64)) :
    ∀ n (s : ArmState), n ≤ words.length →
      CodeAt s base → read_err s = .None → CheckSPAlignment s →
      read_pc s = base + 368#64 →
      r (.GPR 9#5) s = pointer - 8#64 →
      r (.GPR 8#5) s = BitVec.ofNat 64 n →
      NatCompare.Source s pointer words → NatCompare.Words s pointer words →
      ∃ fuel t, run fuel s = t ∧ NatNarrow.Frame s t ∧
        r (.GPR 9#5) t = pointer - 8#64 ∧
        read_pc t = base + BitVec.ofNat 64
          (if significantCount words n = 0 then 2732 else 416) ∧
        (significantCount words n = 0 → r (.GPR 8#5) t = 0#64) ∧
        (significantCount words n ≠ 0 →
          r (.GPR 10#5) t = BitVec.ofNat 64 (significantCount words n) ∧
          r (.GPR 11#5) t = words[significantCount words n - 1]?.getD 0#64) := by
  intro n
  induction n with
  | zero =>
    intro s bound code error aligned pc pointerReg index source memory
    let t := valueBlock base valueGuardOps s
    have follows : ValueFollows base valueGuardOps s := by
      simpa [valueGuardOps, ValueFollows, ValueOp.row] using pc
    refine ⟨1, t, value_run base valueGuardOps s code error aligned follows,
      value_pure_frame base _ s (by decide), ?_, ?_, ?_, ?_⟩
    · simpa [t, valueGuardOps, valueBlock, ValueOp.effect, state_simp_rules] using pointerReg
    · simp [t, valueGuardOps, significantCount, valueBlock, ValueOp.effect,
        state_simp_rules, index]
    · simp [t, valueGuardOps, valueBlock, ValueOp.effect, state_simp_rules, index]
    · simp [significantCount]
  | succ n ih =>
    intro s bound code error aligned pc pointerReg index source memory
    obtain ⟨executed, frame, nextPointer, nextIndex, count, limb, nextPC⟩ :=
      value_scan_round s base pointer words n code error aligned pc pointerReg
        (by omega) index source memory
    let u := valueRoundResult s base (words[n]?.getD 0#64)
    change run 12 s = u at executed
    change NatNarrow.Frame s u at frame
    change r (.GPR 9#5) u = pointer - 8#64 at nextPointer
    change r (.GPR 8#5) u = BitVec.ofNat 64 n at nextIndex
    change r (.GPR 10#5) u = BitVec.ofNat 64 (n + 1) at count
    change r (.GPR 11#5) u = words[n]?.getD 0#64 at limb
    change read_pc u = base + BitVec.ofNat 64
      (if words[n]?.getD 0#64 = 0#64 then 368 else 416) at nextPC
    by_cases zero : words[n]?.getD 0#64 = 0#64
    · obtain ⟨fuel, t, resultRun, resultFrame, resultPointer, resultPC, resultZero, resultTop⟩ :=
        ih u (by omega) (code.congr frame.program) (frame.error.trans error)
          (frame.aligned aligned) (by simpa [zero] using nextPC) nextPointer nextIndex
          (frame.source _ _ source) (frame.words _ _ source memory)
      refine ⟨12 + fuel, t, ?_, frame.trans resultFrame, resultPointer, ?_, ?_, ?_⟩
      · rw [run_plus, executed, resultRun]
      · simpa [significantCount, zero] using resultPC
      · simpa [significantCount, zero] using resultZero
      · simpa [significantCount, zero] using resultTop
    · refine ⟨12, u, executed, frame, nextPointer, ?_, ?_, ?_⟩
      · simpa [significantCount, zero] using nextPC
      · simp [significantCount, zero]
      · intro positive
        simpa [significantCount, zero] using And.intro count limb

end SszArm.Measure.Uint
