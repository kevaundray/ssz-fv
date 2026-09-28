import SszArm.MeasureUintCountFrame
import SszArm.MeasureUintCountMath

namespace SszArm.Measure.Uint

open UintCodec

def countDivideOps : List CountOp :=
  [.p2284, .p2288, .p2292, .p2296, .p2300, .p2304, .p2308, .p2312]

def countDivideResult (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 2736#64)
    (w (.GPR 9#5) (r (.GPR 9#5) s >>> 3)
      (w (.GPR 8#5) ((r (.GPR 8#5) s >>> 3) ||| (r (.GPR 9#5) s <<< 61))
        (NatCompare.saved s 10#5)))

theorem count_divide_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 2284#64) (safe : 16 ≤ (r (.GPR 31#5) s).toNat) :
    run 8 s = countDivideResult s base := by
  have restored : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (NatCompare.saved s 10#5) = r (.GPR 10#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have pc' : r .PC s = base + 2284#64 := pc
  have follows : CountFollows base countDivideOps s := by
    simp [countDivideOps, CountFollows, CountOp.row, CountOp.effect, put, next,
      Emit.Dispatch.next, state_simp_rules, pc', BitVec.add_assoc]
  rw [show 8 = countDivideOps.length by rfl,
    count_run base countDivideOps s code error aligned follows]
  simp only [NatCompare.saved] at restored
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field with
    | GPR reg =>
      by_cases low : reg = 8#5 <;> by_cases high : reg = 9#5 <;>
        by_cases temporary : reg = 10#5 <;> by_cases stack : reg = 31#5 <;>
        (try subst reg) <;>
        simp_all (config := {decide := true, instances := true})
          [countDivideResult, countDivideOps, countBlock, CountOp.effect, put, next,
            Emit.Dispatch.next, NatCompare.saved, state_simp_rules, NatCompare.read_spill_w,
            BitVec.sub_add_cancel, BitVec.add_assoc]
    | PC =>
      simp_all (config := {decide := true, instances := true})
        [countDivideResult, countDivideOps, countBlock, CountOp.effect, put, next,
          Emit.Dispatch.next, NatCompare.saved, state_simp_rules, NatCompare.read_spill_w,
          BitVec.sub_add_cancel, BitVec.add_assoc]
    | SFP reg => simp [countDivideResult, countDivideOps, countBlock, CountOp.effect,
        put, next, Emit.Dispatch.next, NatCompare.saved, state_simp_rules]
    | FLAG flag => simp [countDivideResult, countDivideOps, countBlock, CountOp.effect,
        put, next, Emit.Dispatch.next, NatCompare.saved, state_simp_rules]
    | ERR => simp [countDivideResult, countDivideOps, countBlock, CountOp.effect,
        put, next, Emit.Dispatch.next, NatCompare.saved, state_simp_rules]
  · simp [countDivideResult, countDivideOps, countBlock, CountOp.effect, put, next,
      Emit.Dispatch.next, NatCompare.saved, state_simp_rules]
  · intro count address
    simp [countDivideResult, countDivideOps, countBlock, CountOp.effect, put, next,
      Emit.Dispatch.next, NatCompare.saved, state_simp_rules, NatCompare.read_spill_w]

theorem count_divide_frame (s : ArmState) (base : BitVec 64)
    (safe : 16 ≤ (r (.GPR 31#5) s).toNat) :
    NatNarrow.Frame s (countDivideResult s base) := by
  have frame := NatNarrow.saved_frame s 10#5 safe
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [countDivideResult, state_simp_rules] using frame.program
  · simpa [countDivideResult, state_simp_rules] using frame.error
  · intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    simp (disch := simp_all) [countDivideResult, NatCompare.saved, state_simp_rules]
  · intro reg; simpa [countDivideResult, state_simp_rules] using frame.vectors reg
  · intro address outside
    simpa [countDivideResult, state_simp_rules] using frame.memory address outside

theorem count_divide_value (s : ArmState) (base : BitVec 64) :
    pairValue (r (.GPR 8#5) (countDivideResult s base))
      (r (.GPR 9#5) (countDivideResult s base)) =
      pairValue (r (.GPR 8#5) s) (r (.GPR 9#5) s) / 8 := by
  simpa [countDivideResult, NatCompare.saved, state_simp_rules] using
    count_shr3 (r (.GPR 8#5) s) (r (.GPR 9#5) s)

end SszArm.Measure.Uint
