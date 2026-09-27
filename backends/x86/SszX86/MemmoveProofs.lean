import SszX86.MemmoveLoops

namespace SszX86

/-- The original destination is returned, the genuine return slot is popped,
and every SysV callee-saved register and all SIMD state are preserved. -/
def MemmoveReturned (s : MachineData) (ra : BitVec 64) (t : MachineState) : Prop :=
  t.2 = Int64.ofBitVec ra ∧
  t.1.regs.rax = s.regs.rdi ∧
  t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8#64 ∧
  t.1.zmms = s.zmms ∧
  (∀ r, r ≠ .rax → r ≠ .rsp → r ≠ .rcx → r ≠ .rdx →
    r ≠ .rsi → r ≠ .rdi → r ≠ .r8 → t.1.regs.get64 r = s.regs.get64 r)

private theorem returned_frame (s t : MachineData) (ra : BitVec 64)
    (frame : MemcpyFrame (memmoveEntryState s false) t) :
    MemmoveReturned s ra ({ t with regs := { t.regs with
      rsp := UInt64.ofBitVec (t.regs.rsp.toBitVec + 8) } }, Int64.ofBitVec ra) := by
  refine ⟨rfl, frame.1, ?_, frame.2.2.1, ?_⟩
  · change t.regs.rsp.toBitVec + 8#64 = _
    rw [frame.2.1]
    rfl
  · intro r hrax hrsp hrcx hrdx hrsi hrdi hr8
    have hreg := frame.2.2.2 r hrcx hrdx hrsi hrdi hr8
    cases r <;> simp_all [memmoveEntryState, memcpyTestState, Reg64s.get64]

private theorem entry_frame (s : MachineData) (af : Bool) :
    MemcpyFrame (memmoveEntryState s false) (memmoveEntryState s af) := by
  exact ⟨rfl, rfl, rfl, fun _ _ _ _ _ _ => rfl⟩

/-- Count zero does not require either data pointer to be mapped. Only the
actual RET slot is read. The initial TEST's undefined AF is fully quantified. -/
theorem memmove_zero (base : Int64) (s : MachineData) (ra : BitVec 64)
    (hz : s.regs.rdx.toBitVec = 0#64)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    Eventually (memmoveStep base)
      (fun t => MemmoveReturned s ra t ∧ t.1.dmem = s.dmem) (s, base) := by
  apply memmove_entry_runs
  intro af
  simp only [hz]
  apply memmove_ret_runs base false (memmoveEntryState s af) ra _ hr
  exact ⟨returned_frame s _ ra (entry_frame s af), rfl⟩

/-- Equal pointers return immediately for every representable count, without
reading or writing the data region. No mapped-buffer premise is necessary. -/
theorem memmove_equal (base : Int64) (s : MachineData) (ra : BitVec 64)
    (heq : s.regs.rdi.toBitVec = s.regs.rsi.toBitVec)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    Eventually (memmoveStep base)
      (fun t => MemmoveReturned s ra t ∧ t.1.dmem = s.dmem) (s, base) := by
  by_cases hz : s.regs.rdx.toBitVec = 0#64
  · exact memmove_zero base s ra hz hr
  apply memmove_entry_runs
  intro af
  simp [hz]
  apply memmove_compare_runs
  have hzf : (memmoveCompareState (memmoveEntryState s af)).status.zf = true := by
    change (memcpySubFlags s.regs.rdi.toBitVec s.regs.rsi.toBitVec).zf = true
    simp [memmove_zf_compare, heq]
  rw [hzf]
  simp only [ite_true]
  apply memmove_ret_runs base false (memmoveCompareState (memmoveEntryState s af)) ra _ hr
  exact ⟨returned_frame s _ ra
    (memcpyFrame_trans (entry_frame s af) (memmoveCompare_frame _)), rfl⟩

/-- Consumer-visible result: every destination byte is the ORIGINAL source
snapshot, while every mapped or unmapped lookup outside the destination is exact.
There is deliberately no promise that an overlapping source remains unchanged. -/
def MemmovePost (s : MachineData) (xs : List UInt8) (ra : BitVec 64)
    (t : MachineState) : Prop :=
  MemmoveReturned s ra t ∧
  (∀ i < xs.length, t.1.dmem.get? (s.regs.rdi.toBitVec + BitVec.ofNat 64 i) = xs[i]?) ∧
  (∀ a, (∀ i < xs.length, a ≠ s.regs.rdi.toBitVec + BitVec.ofNat 64 i) →
    t.1.dmem.get? a = s.dmem.get? a)

/-- Complete refinement through real RET at arbitrary code bases and arbitrary
representable counts. Buffers may overlap arbitrarily and their one-past
endpoints may equal `2^64`; accessed bytes themselves are nonwrapping.
The return slot may alias the original source, but no destination byte may
alias it. Code fetch is separate from data memory in the pinned ISA model. -/
theorem memmove_correct (base : Int64) (s : MachineData) (xs : List UInt8)
    (ra : BitVec 64)
    (hcount : s.regs.rdx.toBitVec = BitVec.ofNat 64 xs.length)
    (hb : xs.length < 2^64)
    (input : MoveInput s.dmem s.regs.rsi.toBitVec s.regs.rdi.toBitVec xs.length xs)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (hsep : ∀ i < 8, ∀ j < xs.length,
      s.regs.rsp.toBitVec + BitVec.ofNat 64 i ≠
        s.regs.rdi.toBitVec + BitVec.ofNat 64 j) :
    Eventually (memmoveStep base) (MemmovePost s xs ra) (s, base) := by
  by_cases hz : xs.length = 0
  · have hzreg : s.regs.rdx.toBitVec = 0#64 := by simpa only [hz] using hcount
    have hrun := memmove_zero base s ra hzreg hr
    apply eventually_weaken _ _ _ _ ?_ hrun
    intro t ht
    refine ⟨ht.1, ?_, ?_⟩
    · intro i hi
      omega
    · intro a _
      rw [ht.2]
  by_cases heq : s.regs.rdi.toBitVec = s.regs.rsi.toBitVec
  · have hrun := memmove_equal base s ra heq hr
    apply eventually_weaken _ _ _ _ ?_ hrun
    intro t ht
    refine ⟨ht.1, ?_, ?_⟩
    · intro i hi
      rw [ht.2, heq]
      exact input.source i hi
    · intro a _
      rw [ht.2]
  have hnz : s.regs.rdx.toBitVec ≠ 0#64 := by
    intro he
    have hn := congrArg BitVec.toNat he
    simp only [hcount, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, Nat.zero_mod] at hn
    exact hz hn
  apply memmove_entry_runs
  intro af
  simp [hnz]
  apply memmove_compare_runs
  let t := memmoveCompareState (memmoveEntryState s af)
  have hzf : t.status.zf = false := by
    change (memcpySubFlags s.regs.rdi.toBitVec s.regs.rsi.toBitVec).zf = false
    rw [memmove_zf_compare]
    simp only [heq, decide_false]
  have hcf : t.status.cf = decide (s.regs.rdi.toBitVec.toNat < s.regs.rsi.toBitVec.toNat) :=
    memmove_cf_compare _ _
  have go (back : Bool)
      (direction : MemmoveDirection back s.regs.rsi.toBitVec s.regs.rdi.toBitVec) :
      Eventually (memmoveStep base) (MemmovePost s xs ra)
        (t, if back then base + 69 else base + 15) := by
    have hrun := memmove_direction_runs base back t xs input direction hcount hb
    apply eventually_trans _ _ _ _ hrun
    rintro ⟨u, pc⟩ ⟨hpc, hframe, himage⟩
    change pc = memmoveRetPc base back at hpc
    subst pc
    have hf : MemcpyFrame (memmoveEntryState s false) u :=
      memcpyFrame_trans
        (memcpyFrame_trans (entry_frame s af) (memmoveCompare_frame _)) hframe
    have hrsp : u.regs.rsp = s.regs.rsp := hf.2.1
    have hret : Mem.loadInt u.dmem u.regs.rsp.toBitVec 8 =
        some (Int.ofBytes (wordBytes ra)) := by
      rw [hrsp, memmove_loadInt_frame himage 8 (fun i hi j _ hj => hsep i hi j hj)]
      exact hr
    apply memmove_ret_runs base back u ra _ hret
    exact ⟨returned_frame s u ra hf, memmove_final himage⟩
  rw [hzf]
  simp only [Bool.false_eq_true, ite_false]
  change Eventually (memmoveStep base) (MemmovePost s xs ra)
    (t, if t.status.cf then base + 15 else base + 69)
  by_cases hlt : s.regs.rdi.toBitVec.toNat < s.regs.rsi.toBitVec.toNat
  · have h := go false (Nat.le_of_lt hlt)
    simpa only [hcf, decide_eq_true_eq, hlt, Bool.false_eq_true, ite_false, ite_true] using h
  · have h := go true (by change s.regs.rsi.toBitVec.toNat ≤ s.regs.rdi.toBitVec.toNat; omega)
    simpa only [hcf, decide_eq_true_eq, hlt, Bool.false_eq_true, ite_false, ite_true] using h

end SszX86
