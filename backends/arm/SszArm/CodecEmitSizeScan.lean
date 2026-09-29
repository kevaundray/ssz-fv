import SszArm.CodecEmitSizeScanOps

namespace SszArm.Codec.Emit.SizeScan

open SszNative.Limbs SszArm.Emit.Uint

def guardOps : List WidthOp := [.p80, .p84]
def tailOps : List WidthOp := [.p120, .p124, .p128]

def roundResult (s : ArmState) (base limb : BitVec 64) : ArmState :=
  block base tailOps (scanLoadResult (block base guardOps s) (base + 112#64) limb)

/-- One real backward limb iteration, including the transient lower-stack spill. -/
theorem round (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (index : Nat)
    (code : Linked.EmitParts.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 192#64)
    (address : r (.GPR 8#5) s = pointer) (inside : index < words.length)
    (position : r (.GPR 10#5) s = BitVec.ofNat 64 index)
    (source : NatCompare.Source s pointer words) (stored : NatCompare.Words s pointer words) :
    let t := roundResult s base (words[index]?.getD 0#64)
    run 13 s = t ∧ NatNarrow.Frame s t ∧ r (.GPR 8#5) t = pointer ∧
      r (.GPR 10#5) t = BitVec.ofNat 64 index - 1#64 ∧
      r (.GPR 9#5) t = BitVec.ofNat 64 index ∧
      read_pc t = base + BitVec.ofNat 64
        (if words[index]?.getD 0#64 = 0#64 then 192 else 244) := by
  have countBound : words.length < 2^64 := by have bound := source.2.1; omega
  have nonzero : BitVec.ofNat 64 index + 1#64 ≠ 0#64 := by bv_omega
  let u := block base guardOps s
  change r .PC s = _ at pc
  have follows : Follows base guardOps s := by
    simp [guardOps, Follows, row, effect, WidthOp.row, WidthOp.effect, put, next,
      SszArm.Emit.Dispatch.next, state_simp_rules, pc, BitVec.add_assoc]
  have runGuard : run 2 s = u := runs base guardOps s (by decide) code error aligned follows
  have guardFrame : NatNarrow.Frame s u := pure_frame base _ s (by decide)
  have guardPc : read_pc u = base + 200#64 := by
    simp [u, guardOps, block, effect, WidthOp.effect, put, next,
      SszArm.Emit.Dispatch.next, state_simp_rules, position, nonzero]
  have guardIndex : r (.GPR 10#5) u = BitVec.ofNat 64 index := by
    simpa [u, guardOps, block, effect, WidthOp.effect, put, next,
      SszArm.Emit.Dispatch.next, state_simp_rules] using position
  have guardAddress : r (.GPR 8#5) u = pointer := by
    simpa [u, guardOps, block, effect, WidthOp.effect, put, next,
      SszArm.Emit.Dispatch.next, state_simp_rules] using address
  have sourceU := guardFrame.source pointer words source
  have storedU := guardFrame.words pointer words source stored
  have loaded : read_mem_bytes 8 (r (.GPR 8#5) u + (r (.GPR 10#5) u <<< 3))
      (NatCompare.saved u 9#5) = words[index]?.getD 0#64 := by
    rw [guardIndex, guardAddress]
    exact NatCompare.limb_load u pointer words index 9#5 inside sourceU storedU
  let v := scanLoadResult u (base + 112#64) (words[index]?.getD 0#64)
  have runLoad : run 8 u = v := load_run u base _ (frame_code guardFrame code)
    (guardFrame.error.trans error) (guardFrame.aligned aligned) guardPc sourceU.1 loaded
  have loadFrame : NatNarrow.Frame s v :=
    guardFrame.trans (scan_load_frame u (base + 112#64) _ sourceU.1)
  have tailFollows : Follows base tailOps v := by
    simp [v, tailOps, scanLoadResult, Follows, row, WidthOp.row, effect, WidthOp.effect,
      put, next, SszArm.Emit.Dispatch.next, state_simp_rules, BitVec.add_assoc]
  have runTail : run 3 v = block base tailOps v := runs base tailOps v (by decide)
    (frame_code loadFrame code) (loadFrame.error.trans error)
    (loadFrame.aligned aligned) tailFollows
  refine ⟨?_, loadFrame.trans (pure_frame base _ v (by decide)), ?_, ?_, ?_, ?_⟩
  · rw [show 13 = 2 + 8 + 3 by decide, run_plus, run_plus, runGuard, runLoad, runTail]
    rfl
  all_goals simp [roundResult, tailOps, scanLoadResult, guardOps, block, effect,
    WidthOp.effect, put, next, SszArm.Emit.Dispatch.next, NatCompare.saved,
    state_simp_rules, position, address, BitVec.add_assoc, apply_ite]

/-- The actual emitter loop trims any allocated high-zero suffix. Neither a
limb count cap nor a canonical representation premise is imposed. -/
theorem significant_scan (base pointer : BitVec 64) (words : List (BitVec 64)) :
    ∀ count (s : ArmState), count ≤ words.length →
      Linked.EmitParts.CodeAt s base → read_err s = .None → CheckSPAlignment s →
      read_pc s = base + 192#64 → r (.GPR 8#5) s = pointer →
      r (.GPR 10#5) s = BitVec.ofNat 64 count - 1#64 →
      NatCompare.Source s pointer words → NatCompare.Words s pointer words →
      ∃ fuel t, run fuel s = t ∧ NatNarrow.Frame s t ∧ r (.GPR 8#5) t = pointer ∧
        read_pc t = base + BitVec.ofNat 64
          (if significantCount words count = 0 then 260 else 244) ∧
        (significantCount words count ≠ 0 →
          r (.GPR 9#5) t = BitVec.ofNat 64 (significantCount words count - 1)) := by
  intro count
  induction count with
  | zero =>
    intro s inside code error aligned pc address position source stored
    let t := block base guardOps s
    change r .PC s = _ at pc
    have follows : Follows base guardOps s := by
      simp [guardOps, Follows, row, effect, WidthOp.row, WidthOp.effect, put, next,
        SszArm.Emit.Dispatch.next, state_simp_rules, pc, BitVec.add_assoc]
    refine ⟨2, t, runs base guardOps s (by decide) code error aligned follows,
      pure_frame base _ s (by decide), ?_, ?_, ?_⟩
    · simpa [t, guardOps, block, effect, WidthOp.effect, put, next,
        SszArm.Emit.Dispatch.next, state_simp_rules] using address
    · simp [t, guardOps, significantCount, block, effect, WidthOp.effect, put, next,
        SszArm.Emit.Dispatch.next, state_simp_rules, position]
    · simp [significantCount]
  | succ count ih =>
    intro s inside code error aligned pc address position source stored
    have position' : r (.GPR 10#5) s = BitVec.ofNat 64 count := by
      simpa [BitVec.ofNat_add, BitVec.add_sub_cancel] using position
    obtain ⟨runRound, roundFrame, addressU, indexU, resultU, pcU⟩ :=
      round s base pointer words count code error aligned pc address (by omega)
        position' source stored
    let u := roundResult s base (words[count]?.getD 0#64)
    change run 13 s = u at runRound
    change NatNarrow.Frame s u at roundFrame
    change r (.GPR 8#5) u = pointer at addressU
    change r (.GPR 10#5) u = BitVec.ofNat 64 count - 1#64 at indexU
    change r (.GPR 9#5) u = BitVec.ofNat 64 count at resultU
    change read_pc u = base + BitVec.ofNat 64
      (if words[count]?.getD 0#64 = 0#64 then 192 else 244) at pcU
    by_cases zero : words[count]?.getD 0#64 = 0#64
    · obtain ⟨fuel, t, runRest, restFrame, addressT, pcT, indexT⟩ := ih u (by omega)
        (frame_code roundFrame code) (roundFrame.error.trans error)
        (roundFrame.aligned aligned) (by simpa [zero] using pcU) addressU indexU
        (roundFrame.source _ _ source) (roundFrame.words _ _ source stored)
      refine ⟨13 + fuel, t, ?_, roundFrame.trans restFrame, addressT, ?_, ?_⟩
      · rw [run_plus, runRound, runRest]
      · simpa [significantCount, zero] using pcT
      · simpa [significantCount, zero] using indexT
    · refine ⟨13, u, runRound, roundFrame, addressU, ?_, ?_⟩
      · simpa [significantCount, zero] using pcU
      · intro positive
        simpa [significantCount, zero] using resultU

end SszArm.Codec.Emit.SizeScan
