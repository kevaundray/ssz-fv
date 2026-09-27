import SszX86.MemcpyLoops
import SszX86.MemcpyReturn

namespace SszX86

/-- Return address, original destination, popped stack slot, SIMD state and
all general-purpose registers not used by the copy implementation. -/
def MemcpyReturned (s : MachineData) (ra : BitVec 64) (t : MachineState) : Prop :=
  t.2 = Int64.ofBitVec ra ∧
  t.1.regs.rax = s.regs.rdi ∧
  t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8#64 ∧
  t.1.zmms = s.zmms ∧
  (∀ r, r ≠ .rax → r ≠ .rsp → r ≠ .rcx → r ≠ .rdx →
    r ≠ .rsi → r ≠ .rdi → r ≠ .r8 → t.1.regs.get64 r = s.regs.get64 r)

/-- Empty copies execute the real entry, TEST, branch and RET. Neither data
pointer needs to designate mapped memory; only RET's input slot is read. -/
theorem memcpy_zero (base : Int64) (s : MachineData) (ra : BitVec 64)
    (hz : s.regs.rdx.toBitVec = 0#64)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    Eventually (memcpyStep base)
      (fun t => MemcpyReturned s ra t ∧ t.1.dmem = s.dmem) (s, base) := by
  apply memcpy_entry_runs
  have hc : (memcpyEntryState s).status.cf = true := by
    simp [memcpyEntryState, memcpySubFlags, StatusFlags.from_result, hz, BitVec.unsigned]
  rw [hc]
  simp only [ite_true]
  apply memcpy_tail_runs
  intro af
  have hc0 : ((memcpyEntryState s).regs.rdx.toBitVec == 0) = true := by
    simp [memcpyEntryState, hz]
  rw [hc0]
  simp only [ite_true]
  apply memcpy_ret_runs base _ ra
  · exact hr
  · refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, rfl⟩
    intro r h1 h2 h3 h4 h5 h6 h7
    cases r <;> simp_all [memcpyTestState, memcpyEntryState, Reg64s.get64]

/-- Complete execution through RET at any code base. The readonly return slot
may overlap the source; it must only be disjoint from the destination. The
exact frame identifies every byte outside the destination, not just a property
of an existentially chosen replacement frame. -/
theorem memcpy_correct (base : Int64) (s : MachineData)
    (xs old : List UInt8) (frame : DataMem) (ra : BitVec 64)
    (hlen : old.length = xs.length)
    (hcount : s.regs.rdx.toBitVec = BitVec.ofNat 64 xs.length)
    (hb : xs.length < 2^64)
    (hmem : CopyMem s.dmem s.regs.rsi.toBitVec s.regs.rdi.toBitVec xs old (Eq frame))
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (hsep : ∀ i < 8, ∀ j < xs.length,
      s.regs.rsp.toBitVec + BitVec.ofNat 64 i ≠
        s.regs.rdi.toBitVec + BitVec.ofNat 64 j) :
    Eventually (memcpyStep base) (fun st =>
      MemcpyReturned s ra st ∧
      CopyMem st.1.dmem s.regs.rsi.toBitVec s.regs.rdi.toBitVec xs xs (Eq frame) ∧
      (∀ a, a ∉ xs.At s.regs.rdi.toBitVec → st.1.dmem.get? a = s.dmem.get? a))
      (s, base) := by
  have hrun := memcpy_loops_runs base s xs old (Eq frame) hlen hcount hb hmem
  apply eventually_trans _ _ _ _ hrun
  rintro ⟨t, pc⟩ ⟨hpc, _, hframe, hcopy⟩
  change pc = base + 56 at hpc
  subst pc
  have hcopy' : CopyMem t.dmem s.regs.rsi.toBitVec s.regs.rdi.toBitVec xs xs (Eq frame) :=
    hcopy
  have hrsp : t.regs.rsp = s.regs.rsp := hframe.2.1
  have hret : Mem.loadInt t.dmem t.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)) := by
    rw [hrsp, memcpy_loadInt_rsp_eq hmem hcopy' hlen hsep]
    exact hr
  apply memcpy_ret_runs base t ra _ hret
  refine ⟨⟨rfl, hframe.1, ?_, hframe.2.2.1, ?_⟩, hcopy', ?_⟩
  · change t.regs.rsp.toBitVec + 8#64 = _
    rw [hrsp]
  · intro r hrax hrsp hrcx hrdx hrsi hrdi hr8
    have hreg := hframe.2.2.2 r hrcx hrdx hrsi hrdi hr8
    cases r <;> simp_all [memcpyEntryState, Reg64s.get64]
  · intro a ha
    exact memcpy_lookup_eq_outside_dst hmem hcopy' hlen ha

end SszX86
