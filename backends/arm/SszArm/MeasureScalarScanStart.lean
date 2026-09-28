import SszArm.MeasureScalarVectorClassify

namespace SszArm.Measure.Scalar.Bytes

open Result SszNative.Limbs

def Kind.initialOp : Kind → Op
  | .vector => p1176 | .list => p816

@[irreducible] def scanInitial (kind : Kind) (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 kind.scanGuard)
    (w (.GPR 11#5) (r (.GPR 9#5) s - 1#64) s)

theorem scan_initial_run (kind : Kind) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.largePC) : run 1 s = scanInitial kind s base := by
  have follows : Follows base [kind.initialOp] s := by cases kind <;> exact ⟨error, pc, trivial⟩
  rw [show 1 = [kind.initialOp].length by rfl, runs _ s base code follows]
  change r .PC s = _ at pc
  cases kind <;> simp (config := {decide := true, instances := true})
    [effect, Kind.initialOp, Kind.largePC, Kind.scanGuard, p1176, p816,
     Op.effect, exec_inst, scanInitial, state_simp_rules, bitvec_rules, minimal_theory,
     pc, BitVec.add_assoc, NatExact.gpr_w_pc, w_of_w_shadow]

theorem scan_initial_frame (kind : Kind) (s : ArmState) (base : BitVec 64) :
    NatNarrow.Frame s (scanInitial kind s base) := by
  constructor
  · simp [scanInitial, state_simp_rules]
  · simp [scanInitial, state_simp_rules]
  · intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    simp (disch := simp_all) [scanInitial, state_simp_rules]
  · intro reg; simp [scanInitial, state_simp_rules]
  · intro address outside; simp [scanInitial, state_simp_rules]

theorem large_scan (kind : Kind) (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64))
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.largePC)
    (ptr : r (.GPR 8#5) s = pointer) (count : r (.GPR 9#5) s = BitVec.ofNat 64 words.length)
    (source : NatCompare.Source s pointer words) (stored : NatCompare.Words s pointer words) :
    ∃ fuel t, run fuel s = t ∧ NatNarrow.Frame s t ∧
      (∀ reg ∈ kind.scanKept, r (.GPR reg) t = r (.GPR reg) s) ∧
      read_pc t = base + BitVec.ofNat 64
        (if sigWords words = 0 then kind.scanZero else kind.scanExit) ∧
      (sigWords words ≠ 0 → kind.remembered t = BitVec.ofNat 64 (sigWords words - 1)) := by
  let u := scanInitial kind s base
  have hu : run 1 s = u := scan_initial_run kind s base code error pc
  have uf : NatNarrow.Frame s u := scan_initial_frame kind s base
  have up : read_pc u = base + BitVec.ofNat 64 kind.scanGuard := by
    simp [u, scanInitial, state_simp_rules]
  have upp : r (.GPR 8#5) u = pointer := by
    simpa (config := {decide := true}) [u, scanInitial, state_simp_rules] using ptr
  have ui : r (.GPR 11#5) u = BitVec.ofNat 64 words.length - 1#64 := by
    simp [u, scanInitial, count, state_simp_rules]
  obtain ⟨fuel, t, ht, tf, kept, tp, remembered⟩ := significant_scan kind base pointer words
    words.length u (by omega) (code.congr uf.program) (uf.error.trans error)
    (uf.aligned aligned) up upp ui (uf.source _ _ source) (uf.words _ _ source stored)
  refine ⟨1 + fuel, t, by rw [run_plus, hu, ht], uf.trans tf, ?_, tp, remembered⟩
  intro reg member
  rw [kept reg member]
  cases kind <;> simp only [Kind.scanKept, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals first
    | (rcases member with rfl | rfl | rfl)
    | (rcases member with rfl | rfl)
  all_goals simp (config := {decide := true}) [u, scanInitial, state_simp_rules]

end SszArm.Measure.Scalar.Bytes
