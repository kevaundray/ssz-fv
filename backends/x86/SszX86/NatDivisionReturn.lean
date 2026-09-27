import SszX86.NatDivisionStack

namespace SszX86.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- ADD discards only the scratch word, then six POPs restore the saved GPRs. -/
def restoredState (s original : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 56)
      rbx := original.regs.rbx
      rbp := original.regs.rbp
      r12 := original.regs.r12
      r13 := original.regs.r13
      r14 := original.regs.r14
      r15 := original.regs.r15}
    status := flags}

private theorem bv_add_left_comm {n : Nat} (a b c : BitVec n) :
    a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem u64_add_left_comm (a b c : UInt64) :
    a + (b + c) = b + (a + c) := by
  rw [← UInt64.add_assoc, UInt64.add_comm a b, UInt64.add_assoc]

macro "natdiv_stack_load " hw:term : tactic => `(tactic|
  simp [MachineData.load, Effects.All, ($hw), Delimited.take_cast,
    BitVec.add_comm, bv_add_left_comm, BitVec.add_assoc,
    UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc])

/-- Actual PCs 456–469: discard eight bytes, then restore every callee-saved GPR. -/
theorem restore_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s original : MachineData) (saved : SavedAt s.dmem s.regs.rsp.toBitVec original)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (restoredState s original flags, base + 470)) :
    Eventually (step e) P (s, base + 456) := by
  natdiv_step 115 using hc
  natdiv_step 116 using hc
  natdiv_stack_load saved.rbx
  natdiv_step 117 using hc
  natdiv_stack_load saved.r12
  natdiv_step 118 using hc
  natdiv_stack_load saved.r13
  natdiv_step 119 using hc
  natdiv_stack_load saved.r14
  natdiv_step 120 using hc
  natdiv_stack_load saved.r15
  natdiv_step 121 using hc
  natdiv_stack_load saved.rbp
  simpa [restoredState, BitVec.add_assoc, BitVec.add_comm, bv_add_left_comm,
    UInt64.add_comm, u64_add_left_comm, UInt64.add_assoc,
    show (8 : UInt64) + 48 = 56 by decide] using hp _

/-- RET reads but does not overwrite its physical incoming return slot. -/
def retState (s : MachineData) : MachineData :=
  {s with regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec + 8)}}

theorem ret_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ra : BitVec 64) (P : MachineState → Prop)
    (hr : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (hp : Eventually (step e) P (retState s, Int64.ofBitVec ra)) :
    Eventually (step e) P (s, base + 470) := by
  natdiv_step 122 using hc
  simp only [MachineData.load, Effects.All, hr, ofBytes_wordBytes]
  exact hp

def exitState (s original : MachineData) (flags : StatusFlags) : MachineData :=
  retState (restoredState s original flags)

/-- The complete real epilogue is a continuation rule, not a postulated return. -/
theorem epilogue_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s original : MachineData) (ra : BitVec 64)
    (saved : SavedAt s.dmem s.regs.rsp.toBitVec original)
    (hr : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 56) 8 =
      some (Int.ofBytes (wordBytes ra)))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P (exitState s original flags, Int64.ofBitVec ra)) :
    Eventually (step e) P (s, base + 456) := by
  apply restore_cps e base hc s original saved P
  intro flags
  apply ret_cps e base hc (restoredState s original flags) ra P
  · exact hr
  · exact hp flags

/-- Abstract epilogue summary: only flags and the stack/register restorations change. -/
structure ExitFrame (s original t : MachineData) : Prop where
  memory : t.dmem = s.dmem
  vectors : t.zmms = s.zmms
  stack : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 64
  rbx : t.regs.rbx = original.regs.rbx
  rbp : t.regs.rbp = original.regs.rbp
  r12 : t.regs.r12 = original.regs.r12
  r13 : t.regs.r13 = original.regs.r13
  r14 : t.regs.r14 = original.regs.r14
  r15 : t.regs.r15 = original.regs.r15
  other : ∀ r, r ≠ .rsp → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 →
    r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → t.regs.get64 r = s.regs.get64 r

theorem exit_frame (s original : MachineData) (flags : StatusFlags) :
    ExitFrame s original (exitState s original flags) := by
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · change (s.regs.rsp.toBitVec + 56) + 8 = s.regs.rsp.toBitVec + 64
    bv_omega
  · intro r h1 h2 h3 h4 h5 h6 h7
    cases r <;> simp_all [exitState, retState, restoredState, Reg64s.get64]

/-- The physical incoming RSP, rather than a late register value, fixes the ABI exit. -/
theorem exit_stack (s original : MachineData) (flags : StatusFlags)
    (hsp : s.regs.rsp.toBitVec = original.regs.rsp.toBitVec - 56) :
    (exitState s original flags).regs.rsp.toBitVec = original.regs.rsp.toBitVec + 8 := by
  rw [(exit_frame s original flags).stack, hsp]
  bv_omega

end SszX86.NatDivision
