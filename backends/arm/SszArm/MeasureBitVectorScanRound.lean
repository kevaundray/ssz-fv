import SszArm.MeasureBitVectorScanTail

namespace SszArm.Measure.BitVector

open Result SszNative.Limbs

@[irreducible] def scanRoundResult (s : ArmState) (base limb : BitVec 64) : ArmState :=
  scanTailResult (scanLoadResult (scanGuardResult s base) base limb) base

theorem scan_round (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 592#64)
    (ptr : r (.GPR 11#5) s = pointer) (inside : n < words.length)
    (index : r (.GPR 13#5) s = BitVec.ofNat 64 n)
    (source : NatCompare.Source s pointer words) (stored : NatCompare.Words s pointer words) :
    let t := scanRoundResult s base (words[n]?.getD 0#64)
    run 13 s = t ∧ ScanFrame s t ∧ r (.GPR 9#5) t = r (.GPR 9#5) s ∧
      r (.GPR 13#5) t = BitVec.ofNat 64 n - 1#64 ∧
      r (.GPR 12#5) t = BitVec.ofNat 64 n ∧
      read_pc t = base + BitVec.ofNat 64 (if words[n]?.getD 0#64 = 0#64 then 592 else 644) := by
  have bound : words.length < 2^64 := by have := source.2.1; omega
  have nonzero : BitVec.ofNat 64 n + 1#64 ≠ 0#64 := by bv_omega
  let u := scanGuardResult s base
  have hu : run 2 s = u := scan_guard_run s base code error pc
  have uf : ScanFrame s u := scan_guard_frame s base
  have up : read_pc u = base + 600#64 := by
    simp [u, scanGuardResult, state_simp_rules, index, nonzero]
  have ui : r (.GPR 13#5) u = BitVec.ofNat 64 n := by
    simpa only [u, scan_guard_register] using index
  have upp : r (.GPR 11#5) u = pointer := by
    simpa only [u, scan_guard_register] using ptr
  have us := uf.source pointer words source
  have um := uf.words pointer words source stored
  have loaded : read_mem_bytes 8 (r (.GPR 11#5) u + (r (.GPR 13#5) u <<< 3))
      (NatCompare.saved u 9#5) = words[n]?.getD 0#64 := by
    rw [upp, ui]
    exact NatCompare.limb_load u pointer words n 9#5 inside us um
  let v := scanLoadResult u base (words[n]?.getD 0#64)
  have hv : run 8 u = v := scan_load_run u base _ (code.congr uf.program)
    (uf.error.trans error) (uf.aligned aligned) up us.1 loaded
  have vf : ScanFrame s v := uf.trans (scan_load_frame u base _ us.1)
  have vp : read_pc v = base + 632#64 := by
    simp [v, scanLoadResult, state_simp_rules]
  have ht : run 3 v = scanTailResult v base :=
    scan_tail_run v base (code.congr vf.program) (vf.error.trans error) vp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 13 = 2 + 8 + 3 by omega, run_plus, run_plus, hu, hv, ht]
    simp only [scanRoundResult, v, u]
  · simpa only [scanRoundResult, v, u] using vf.trans (scan_tail_frame v base)
  all_goals
    simp (config := {decide := true})
      [scanRoundResult, scanTailResult, scanLoadResult, scanGuardResult,
       NatCompare.saved, state_simp_rules, index]
  all_goals split <;> rfl

end SszArm.Measure.BitVector
