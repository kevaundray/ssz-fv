import SszX86.MemcmpExec

namespace SszX86.Memcmp

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def Finished (base : Int64) (s : MachineData) (xs : Bytes) (t : MachineState) : Prop :=
  t.2 = base + 31 ∧ (t.1.regs.rax.toBitVec.setWidth 32).toInt = spec xs ∧ Frame s t.1

/-- Structural induction on independently mapped byte pairs. An unequal pair
returns immediately; equal pairs consume exactly one remaining byte. -/
theorem loop_runs (base : Int64) (xs : Bytes) (s : MachineData)
    (hn : s.regs.rdx.toBitVec = BitVec.ofNat 64 xs.length)
    (hb : xs.length < 2^64)
    (hm : Reads s.dmem s.regs.rdi.toBitVec s.regs.rsi.toBitVec xs)
    (hz : xs = [] → (s.regs.rax.toBitVec.setWidth 32).toInt = 0) :
    Eventually (step base) (Finished base s xs)
      (s, if xs = [] then base + 31 else base + 7) := by
  induction xs generalizing s with
  | nil =>
    exact Eventually.done _ ⟨rfl, hz rfl, frame_refl s⟩
  | cons ab xs ih =>
    rcases ab with ⟨a, b⟩
    rcases hm with ⟨ha, hbload, hm⟩
    simp only [List.cons_ne_nil, ite_false]
    apply compare_runs base s a b _ ha hbload
    by_cases hab : a = b
    · subst b
      simp only [ite_true]
      apply advance_runs
      let t := advance (compare s a a)
      have hframe : Frame s t := frame_trans (compare_frame s a a)
        (advance_frame (compare s a a))
      have hn' : t.regs.rdx.toBitVec = BitVec.ofNat 64 xs.length := by
        change s.regs.rdx.toBitVec - 1#64 = _
        rw [hn]
        simp only [List.length_cons]
        bv_omega
      have hm' : Reads t.dmem t.regs.rdi.toBitVec t.regs.rsi.toBitVec xs := hm
      have hz' : xs = [] → (t.regs.rax.toBitVec.setWidth 32).toInt = 0 := by
        intro _
        simp [t, advance, compare]
      have hrec := ih t hn' (by simp only [List.length_cons] at hb; omega) hm' hz'
      have hzf : t.status.zf = decide (xs = []) := by
        change (memcpySubFlags s.regs.rdx.toBitVec 1#64).zf = _
        rw [hn, memcpy_zf_sub1 _ hb]
        simp
      have hstrength : ∀ st, Finished base t xs st → Finished base s ((a, a) :: xs) st := by
        intro st h
        exact ⟨h.1, by simpa [spec] using h.2.1, frame_trans hframe h.2.2⟩
      have hrec' := eventually_weaken _ _ _ _ hstrength hrec
      change Eventually (step base) (Finished base s ((a, a) :: xs))
        (t, if t.status.zf then base + 31 else base + 7)
      simpa only [hzf, decide_eq_true_eq] using hrec'
    · simp only [ite_eq_right hab]
      apply Eventually.done
      refine ⟨rfl, ?_, compare_frame s a b⟩
      simpa [compare, spec, hab] using byte_difference a b

/-- Complete ABI and exact read-only memory postcondition. The C int is the
signed low EAX value, even when hardware zero-extends a negative result in RAX. -/
def Returned (s : MachineData) (ra : BitVec 64) (value : Int) (t : MachineState) : Prop :=
  t.2 = Int64.ofBitVec ra ∧
  (t.1.regs.rax.toBitVec.setWidth 32).toInt = value ∧
  t.1.dmem = s.dmem ∧ t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8 ∧
  t.1.zmms = s.zmms ∧
  (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rdi → r ≠ .rsi → r ≠ .rsp →
    t.1.regs.get64 r = s.regs.get64 r)

/-- Arbitrary code base and representable count; no separation of source views
or of either source from RET's slot is assumed. No bytes beyond the count are
required to be mapped. Entire memory, including mappings, is unchanged. -/
theorem program_correct (base : Int64) (s : MachineData) (xs : Bytes) (ra : BitVec 64)
    (hn : s.regs.rdx.toBitVec = BitVec.ofNat 64 xs.length)
    (hb : xs.length < 2^64)
    (hm : Reads s.dmem s.regs.rdi.toBitVec s.regs.rsi.toBitVec xs)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    Eventually (step base) (Returned s ra (spec xs)) (s, base) := by
  apply entry_runs
  intro af
  have hloops := loop_runs base xs (entry s af) hn hb hm (by intro _; rfl)
  have hzero : (s.regs.rdx.toBitVec == 0) = decide (xs = []) := by
    rw [hn]
    have hn0 : BitVec.ofNat 64 xs.length = 0#64 ↔ xs = [] := by
      constructor
      · intro h
        simpa [Nat.mod_eq_of_lt hb] using congrArg BitVec.toNat h
      · intro h
        simp [h]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    exact hn0
  rw [hzero]
  simp only [decide_eq_true_eq]
  apply eventually_trans _ _ _ _ hloops
  rintro ⟨t, pc⟩ ⟨hpc, hvalue, hf⟩
  change pc = base + 31 at hpc
  subst pc
  have hframe : Frame s t := frame_trans (entry_frame s af) hf
  have hret : Mem.loadInt t.dmem t.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)) := by
    rw [hframe.1, hframe.2.1]
    exact hr
  apply ret_runs base t ra _ hret
  refine ⟨rfl, hvalue, hframe.1, ?_, hframe.2.2.1, ?_⟩
  · change t.regs.rsp.toBitVec + 8#64 = _
    rw [hframe.2.1]
    rfl
  · intro r h1 h2 h3 h4 h5 h6
    have hh := hframe.2.2.2 r h1 h2 h3 h4 h5
    cases r <;> simp_all [Reg64s.get64]

/-- Empty comparison does not dereference either input pointer. -/
theorem program_zero (base : Int64) (s : MachineData) (ra : BitVec 64)
    (hz : s.regs.rdx.toBitVec = 0#64)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    Eventually (step base) (Returned s ra 0) (s, base) :=
  program_correct base s [] ra hz (by decide) trivial hr

/-- Public first-difference linkage: the observable C int is the exact unsigned
subtraction at the earliest mismatch, not merely its sign. -/
theorem program_first_difference (base : Int64) (s : MachineData)
    (pre suffix : Bytes) (a b : BitVec 8) (ra : BitVec 64)
    (heq : ∀ ab ∈ pre, ab.1 = ab.2) (hne : a ≠ b)
    (hn : s.regs.rdx.toBitVec = BitVec.ofNat 64 (pre ++ (a, b) :: suffix).length)
    (hb : (pre ++ (a, b) :: suffix).length < 2^64)
    (hm : Reads s.dmem s.regs.rdi.toBitVec s.regs.rsi.toBitVec (pre ++ (a, b) :: suffix))
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    Eventually (step base) (Returned s ra ((a.toNat : Int) - b.toNat)) (s, base) := by
  simpa only [spec_first_difference pre suffix a b heq hne] using
    program_correct base s (pre ++ (a, b) :: suffix) ra hn hb hm hr

/-- Equal nonempty buffers return zero as well; equality is unsigned bytewise. -/
theorem program_all_equal (base : Int64) (s : MachineData) (xs : Bytes) (ra : BitVec 64)
    (heq : ∀ ab ∈ xs, ab.1 = ab.2)
    (hn : s.regs.rdx.toBitVec = BitVec.ofNat 64 xs.length) (hb : xs.length < 2^64)
    (hm : Reads s.dmem s.regs.rdi.toBitVec s.regs.rsi.toBitVec xs)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    Eventually (step base) (Returned s ra 0) (s, base) := by
  simpa only [spec_all_equal xs heq] using program_correct base s xs ra hn hb hm hr

end SszX86.Memcmp
