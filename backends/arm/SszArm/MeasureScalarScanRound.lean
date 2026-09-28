import SszArm.MeasureScalarScanTail

namespace SszArm.Measure.Scalar.Bytes

open Result SszNative.Limbs

def Kind.scanKept : Kind → List (BitVec 5)
  | .vector => [8#5, 9#5]
  | .list => [8#5, 9#5, 10#5]

def Kind.remembered (kind : Kind) (s : ArmState) : BitVec 64 :=
  match kind with
  | .vector => r (.GPR 10#5) s
  | .list => r (.GPR 11#5) s + 1#64

@[irreducible] def scanRoundResult (kind : Kind) (s : ArmState)
    (base limb : BitVec 64) : ArmState :=
  scanTailResult kind (scanLoadResult kind (scanGuardResult kind s base) base limb) base

theorem scan_round (kind : Kind) (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.scanGuard)
    (ptr : r (.GPR 8#5) s = pointer) (inside : n < words.length)
    (index : r (.GPR 11#5) s = BitVec.ofNat 64 n)
    (source : NatCompare.Source s pointer words) (stored : NatCompare.Words s pointer words) :
    let t := scanRoundResult kind s base (words[n]?.getD 0#64)
    run (10 + kind.tailOps.length) s = t ∧ NatNarrow.Frame s t ∧
      (∀ reg ∈ kind.scanKept, r (.GPR reg) t = r (.GPR reg) s) ∧
      r (.GPR 11#5) t = BitVec.ofNat 64 n - 1#64 ∧
      kind.remembered t = BitVec.ofNat 64 n ∧
      read_pc t = base + BitVec.ofNat 64
        (if words[n]?.getD 0#64 = 0#64 then kind.scanGuard else kind.scanExit) := by
  have bound : words.length < 2^64 := by have := source.2.1; omega
  have nonzero : BitVec.ofNat 64 n + 1#64 ≠ 0#64 := by bv_omega
  let u := scanGuardResult kind s base
  have hu : run 2 s = u := scan_guard_run kind s base code error pc
  have uf : NatNarrow.Frame s u := scan_guard_frame kind s base
  have up : read_pc u = base + BitVec.ofNat 64 kind.scanLoad := by
    simp [u, scanGuardResult, state_simp_rules, index, nonzero]
  have ui : r (.GPR 11#5) u = BitVec.ofNat 64 n := by
    simpa only [u, scan_guard_register] using index
  have upp : r (.GPR 8#5) u = pointer := by simpa only [u, scan_guard_register] using ptr
  have us := uf.source pointer words source
  have um := uf.words pointer words source stored
  have loaded : read_mem_bytes 8 (r (.GPR 8#5) u + (r (.GPR 11#5) u <<< 3))
      (NatCompare.saved u 9#5) = words[n]?.getD 0#64 := by
    rw [upp, ui]
    exact NatCompare.limb_load u pointer words n 9#5 inside us um
  let v := scanLoadResult kind u base (words[n]?.getD 0#64)
  have hv : run 8 u = v := scan_load_run kind u base _ (code.congr uf.program)
    (uf.error.trans error) (uf.aligned aligned) up us.1 loaded
  have vf : NatNarrow.Frame s v := uf.trans (scan_load_frame kind u base _ us.1)
  have vp : read_pc v = base + BitVec.ofNat 64 kind.scanTail := by
    simp [v, scanLoadResult, state_simp_rules]
  have ht : run kind.tailOps.length v = scanTailResult kind v base :=
    scan_tail_run kind v base (code.congr vf.program) (vf.error.trans error) vp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 10 + kind.tailOps.length = 2 + 8 + kind.tailOps.length by omega,
      run_plus, run_plus, hu, hv, ht]
    simp only [scanRoundResult, u, v]
  · simpa only [scanRoundResult, u, v] using vf.trans (scan_tail_frame kind v base)
  · intro reg member
    cases kind <;> simp only [Kind.scanKept, List.mem_cons, List.not_mem_nil, or_false] at member
    all_goals first
      | (rcases member with rfl | rfl | rfl)
      | (rcases member with rfl | rfl)
    all_goals simp (config := {decide := true})
      [scanRoundResult, scanTailResult, scanLoadResult, scanGuardResult,
       NatCompare.saved, state_simp_rules]
  all_goals cases kind <;> simp (config := {decide := true})
    [scanRoundResult, scanTailResult, scanLoadResult, scanGuardResult, Kind.remembered,
     NatCompare.saved, state_simp_rules, index, BitVec.sub_add_cancel]

end SszArm.Measure.Scalar.Bytes
