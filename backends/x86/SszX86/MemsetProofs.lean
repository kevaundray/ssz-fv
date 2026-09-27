import SszX86.MemsetLoops
import SszX86.MemsetReturn

namespace SszX86

/-- Return address, original destination, popped stack slot, SIMD state and all
general-purpose registers not used by the fill implementation. -/
def MemsetReturned (s : MachineData) (ra : BitVec 64) (t : MachineState) : Prop :=
  t.2 = Int64.ofBitVec ra ∧
  t.1.regs.rax = s.regs.rdi ∧
  t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8#64 ∧
  t.1.zmms = s.zmms ∧
  (∀ r, r ≠ .rax → r ≠ .rsp → r ≠ .rdi → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 →
    t.1.regs.get64 r = s.regs.get64 r)

/-- Empty fills execute the real guard, TEST, branch and RET, without executing
the broadcast. The destination need not be mapped; only RET's slot is read. -/
theorem memset_zero (base : Int64) (s : MachineData) (ra : BitVec 64)
    (hz : s.regs.rdx.toBitVec = 0#64)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    Eventually (memsetStep base)
      (fun t => MemsetReturned s ra t ∧ t.1.dmem = s.dmem) (s, base) := by
  apply memset_entry_runs
  have hc : (memcpyEntryState s).status.cf = true := by
    simp [memcpyEntryState, memcpySubFlags, StatusFlags.from_result, hz, BitVec.unsigned]
  rw [hc]
  simp only [ite_true]
  apply memset_tail_runs
  intro af
  have hc0 : ((memcpyEntryState s).regs.rdx.toBitVec == 0) = true := by
    simp [memcpyEntryState, hz]
  rw [hc0]
  simp only [ite_true]
  apply memset_ret_runs base _ ra
  · exact hr
  · refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, rfl⟩
    intro r h1 h2 h3 h4 h5 h6
    cases r <;> simp_all [memsetTestState, memcpyEntryState, Reg64s.get64]

/-- Complete ISA execution through the actual RET, at any code base and for any
representable count. The fill byte is the low byte of RSI, not an unconstrained
parameter. Only the destination and return slot must be disjoint; there is no
source region. The exact original frame and every byte outside the destination
are preserved, along with the ABI registers and the returned destination. -/
theorem memset_correct (base : Int64) (s : MachineData) (n : Nat)
    (old : List UInt8) (frame : DataMem) (ra : BitVec 64)
    (hlen : old.length = n)
    (hcount : s.regs.rdx.toBitVec = BitVec.ofNat 64 n)
    (hb : n < 2^64)
    (hmem : FillMem s.dmem s.regs.rdi.toBitVec old (Eq frame))
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (hsep : ∀ i < 8, ∀ j < n,
      s.regs.rsp.toBitVec + BitVec.ofNat 64 i ≠
        s.regs.rdi.toBitVec + BitVec.ofNat 64 j) :
    Eventually (memsetStep base) (fun st =>
      MemsetReturned s ra st ∧
      FillMem st.1.dmem s.regs.rdi.toBitVec (List.replicate n (memsetByte s)) (Eq frame) ∧
      (∀ a, a ∉ (List.replicate n (memsetByte s)).At s.regs.rdi.toBitVec →
        st.1.dmem.get? a = s.dmem.get? a))
      (s, base) := by
  have hrun := memset_loops_runs base s n old (Eq frame) hlen hcount hb hmem
  apply eventually_trans _ _ _ _ hrun
  rintro ⟨t, pc⟩ ⟨hpc, _, hframe, hfill⟩
  change pc = base + 62 at hpc
  subst pc
  have hfill' : FillMem t.dmem s.regs.rdi.toBitVec
      (List.replicate n (memsetByte s)) (Eq frame) := hfill
  have hrsp : t.regs.rsp = s.regs.rsp := hframe.2.1
  have hlen' : old.length = (List.replicate n (memsetByte s)).length := by
    simpa using hlen
  have hsep' : ∀ i < 8, ∀ j < (List.replicate n (memsetByte s)).length,
      s.regs.rsp.toBitVec + BitVec.ofNat 64 i ≠
        s.regs.rdi.toBitVec + BitVec.ofNat 64 j := by
    simpa using hsep
  have hret : Mem.loadInt t.dmem t.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)) := by
    rw [hrsp, memset_loadInt_rsp_eq hmem hfill' hlen' hsep']
    exact hr
  apply memset_ret_runs base t ra _ hret
  refine ⟨⟨rfl, hframe.1, ?_, hframe.2.2.1, ?_⟩, hfill', ?_⟩
  · change t.regs.rsp.toBitVec + 8#64 = _
    rw [hrsp]
  · intro r hrax hrsp hrdi hrdx hr8 hr9
    have hreg := hframe.2.2.2 r hrdi hrdx hr8 hr9
    cases r <;> simp_all [memcpyEntryState, Reg64s.get64]
  · intro a ha
    exact memset_lookup_eq_outside_dst hmem hfill' hlen' ha

end SszX86
