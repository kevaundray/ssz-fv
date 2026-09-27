import SszArm.MemcmpExec

namespace SszArm.Memcmp

open BitVec

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def Finished (base : BitVec 64) (s : ArmState) (xs : Bytes) (t : ArmState) : Prop :=
  read_pc t = base + 36#64 ∧ ((r (.GPR 0) t).setWidth 32).toInt = spec xs ∧ Frame s t

/-- Finite execution of the byte loop, proved by induction on the remaining
paired read views. Equality alone reaches the decrement and next iteration. -/
theorem loop_runs (base : BitVec 64) (xs : Bytes) (s : ArmState)
    (hc : CodeAt s base program) (he : read_err s = .None)
    (hp : read_pc s = if xs = [] then base + 36#64 else base + 12#64)
    (hn : r (.GPR 2) s = BitVec.ofNat 64 xs.length) (hb : xs.length < 2^64)
    (hm : Reads s.mem (r (.GPR 3) s) (r (.GPR 1) s) xs)
    (hz : xs = [] → ((r (.GPR 0) s).setWidth 32).toInt = 0) :
    ∃ t, Reaches s t ∧ Finished base s xs t := by
  induction xs generalizing s with
  | nil =>
    exact ⟨s, reaches_refl s, by simpa using hp, hz rfl, frame_refl s⟩
  | cons ab xs ih =>
    rcases ab with ⟨a, b⟩
    rcases hm with ⟨ha, hbload, hm⟩
    have hp' : read_pc s = base + 12#64 := by simpa using hp
    have hrun : Reaches s (compare s) := ⟨4, run_compare s base hc hp' he⟩
    have hdata := compare_data s a b ha hbload
    have hpc := compare_pc s base a b hp' ha hbload
    by_cases hab : a = b
    · let u := compare s
      let t := advance u
      have hf : Frame s t := frame_trans (compare_frame s) (advance_frame u)
      have huc : CodeAt u base program := by
        simpa only [u, CodeAt, (compare_frame s).2.1] using hc
      have hue : read_err u = .None := ((compare_frame s).2.2 .ERR trivial).trans he
      have hup : read_pc u = base + 28#64 := by simpa only [if_pos hab] using hpc
      have hrun' : Reaches u t := ⟨2, run_advance u base huc hup hue⟩
      have htc : CodeAt t base program := by simpa only [CodeAt, hf.2.1] using hc
      have hte : read_err t = .None := (hf.2.2 .ERR trivial).trans he
      have htn : r (.GPR 2) t = BitVec.ofNat 64 xs.length := by
        rw [(advance_data u).2.2.1, hdata.2.2.1, hn]
        simp only [List.length_cons]
        bv_omega
      have htp : read_pc t = if xs = [] then base + 36#64 else base + 12#64 := by
        rw [advance_pc u base hup]
        have hzero : r (.GPR 2) u - 1#64 = 0#64 ↔ xs = [] := by
          rw [hdata.2.2.1, hn]
          have hlen : xs.length < 2^64 := by simp only [List.length_cons] at hb; omega
          constructor
          · intro h
            have hn' : xs.length = 0 := by simp only [List.length_cons] at h; bv_omega
            exact List.eq_nil_of_length_eq_zero hn'
          · intro h
            simp [h]
        simp only [hzero]
      have htm : Reads t.mem (r (.GPR 3) t) (r (.GPR 1) t) xs := by
        rw [hf.1, (advance_data u).2.2.2, (advance_data u).2.1,
          hdata.2.2.2, hdata.2.1]
        exact hm
      have htz : xs = [] → ((r (.GPR 0) t).setWidth 32).toInt = 0 := by
        intro _
        rw [(advance_data u).1, hdata.1, hab]
        simp
      obtain ⟨v, hv, hfinish⟩ := ih t htc hte htp htn
        (by simp only [List.length_cons] at hb; omega) htm htz
      refine ⟨v, reaches_trans hrun (reaches_trans hrun' hv), hfinish.1, ?_,
        frame_trans hf hfinish.2.2⟩
      simpa only [spec, if_pos hab] using hfinish.2.1
    · refine ⟨compare s, hrun, ?_, ?_, compare_frame s⟩
      · simpa [hab] using hpc
      · rw [hdata.1]
        simpa [spec, hab] using byte_difference a b

/-- Signed low W0 C-int result, exact memory and immutable code, real return,
all ABI-preserved state, and absence of model execution errors. -/
def Returned (s : ArmState) (value : Int) (t : ArmState) : Prop :=
  Frame s t ∧ read_pc t = r (.GPR 30) s ∧
  ((r (.GPR 0) t).setWidth 32).toInt = value ∧ read_err t = .None

/-- Total literal execution through RET for any code base and representable
count. Source buffers may overlap arbitrarily; every accessed byte is within
the stated views. There is no memory modification at any address. -/
theorem program_correct (s : ArmState) (base : BitVec 64) (xs : Bytes)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None)
    (hn : r (.GPR 2) s = BitVec.ofNat 64 xs.length) (hb : xs.length < 2^64)
    (hm : Reads s.mem (r (.GPR 0) s) (r (.GPR 1) s) xs) :
    ∃ cycles, Returned s (spec xs) (run cycles s) := by
  have hf := entry_frame s
  have hdata := entry_data s
  have hc' : CodeAt (entry s) base program := by simpa only [CodeAt, hf.2.1] using hc
  have he' : read_err (entry s) = .None := (hf.2.2 .ERR trivial).trans he
  have hz : r (.GPR 2) s = 0#64 ↔ xs = [] := by
    rw [hn]
    constructor
    · intro h
      simpa [Nat.mod_eq_of_lt hb] using congrArg BitVec.toNat h
    · intro h
      simp [h]
  have hp' : read_pc (entry s) = if xs = [] then base + 36#64 else base + 12#64 := by
    rw [entry_pc s base hp]
    simp only [hz]
  have hn' : r (.GPR 2) (entry s) = BitVec.ofNat 64 xs.length := hdata.2.2.1.trans hn
  have hm' : Reads (entry s).mem (r (.GPR 3) (entry s)) (r (.GPR 1) (entry s)) xs := by
    rw [hf.1, hdata.2.2.2, hdata.2.1]
    exact hm
  obtain ⟨t, hrun, hfinish⟩ := loop_runs base xs (entry s) hc' he' hp' hn' hb hm'
    (by intro _; rw [hdata.1]; rfl)
  have hft : Frame s t := frame_trans hf hfinish.2.2
  have htc : CodeAt t base program := by simpa only [CodeAt, hft.2.1] using hc
  have hte : read_err t = .None := (hft.2.2 .ERR trivial).trans he
  have hret := step_code t base 9 (by decide) htc (by simpa using hfinish.1) hte
  have htotal : Reaches s (instruction 9 t) :=
    reaches_trans ⟨3, run_entry s base hc hp he⟩
      (reaches_trans hrun ⟨1, hret⟩)
  rcases htotal with ⟨cycles, hcycles⟩
  refine ⟨cycles, ?_⟩
  rw [hcycles]
  refine ⟨frame_trans hft (instruction_full_frame 9 t), ?_, ?_, ?_⟩
  · have hlr := hft.2.2 (.GPR 30) (by simp [Preserved])
    simpa (config := {decide := true}) [instruction, state_simp_rules] using hlr
  · simpa (config := {decide := true}) [instruction, state_simp_rules] using hfinish.2.1
  · exact (instruction_err 9 t).trans hte

/-- Zero count returns in exactly four instructions without observing memory
at either input pointer. In particular no mapping premise is needed. -/
theorem program_zero (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None)
    (hn : r (.GPR 2) s = 0#64) : Returned s 0 (run 4 s) := by
  have hf := entry_frame s
  have hc' : CodeAt (entry s) base program := by simpa only [CodeAt, hf.2.1] using hc
  have he' : read_err (entry s) = .None := (hf.2.2 .ERR trivial).trans he
  have hp' : read_pc (entry s) = base + 36#64 := by
    simpa only [hn, ite_true] using entry_pc s base hp
  have hret := step_code (entry s) base 9 (by decide) hc' (by simpa using hp') he'
  have hrun : run 4 s = instruction 9 (entry s) := by
    change run (3 + 1) s = _
    rw [run_plus, run_entry s base hc hp he]
    exact hret
  rw [hrun]
  refine ⟨frame_trans hf (instruction_full_frame 9 _), ?_, ?_, ?_⟩
  · have hlr := hf.2.2 (.GPR 30) (by simp [Preserved])
    simpa (config := {decide := true}) [instruction, state_simp_rules] using hlr
  · have hg : r (.GPR 0) (instruction 9 (entry s)) = r (.GPR 0) (entry s) := by
      simp (config := {decide := true}) [instruction, state_simp_rules]
    rw [hg, (entry_data s).1]
    rfl
  · exact (instruction_err 9 (entry s)).trans he'

/-- First-difference linkage for the observable signed C int. -/
theorem program_first_difference (s : ArmState) (base : BitVec 64)
    (pre suffix : Bytes) (a b : BitVec 8)
    (heq : ∀ ab ∈ pre, ab.1 = ab.2) (hne : a ≠ b)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None)
    (hn : r (.GPR 2) s = BitVec.ofNat 64 (pre ++ (a, b) :: suffix).length)
    (hb : (pre ++ (a, b) :: suffix).length < 2^64)
    (hm : Reads s.mem (r (.GPR 0) s) (r (.GPR 1) s) (pre ++ (a, b) :: suffix)) :
    ∃ cycles, Returned s ((a.toNat : Int) - b.toNat) (run cycles s) := by
  simpa only [spec_first_difference pre suffix a b heq hne] using
    program_correct s base (pre ++ (a, b) :: suffix) hc hp he hn hb hm

/-- Equal buffers return zero, including when their views overlap. -/
theorem program_all_equal (s : ArmState) (base : BitVec 64) (xs : Bytes)
    (heq : ∀ ab ∈ xs, ab.1 = ab.2)
    (hc : CodeAt s base program) (hp : read_pc s = base) (he : read_err s = .None)
    (hn : r (.GPR 2) s = BitVec.ofNat 64 xs.length) (hb : xs.length < 2^64)
    (hm : Reads s.mem (r (.GPR 0) s) (r (.GPR 1) s) xs) :
    ∃ cycles, Returned s 0 (run cycles s) := by
  simpa only [spec_all_equal xs heq] using program_correct s base xs hc hp he hn hb hm

end SszArm.Memcmp
