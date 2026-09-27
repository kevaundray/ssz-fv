import SszX86.NatDivisionStack
import SszX86.Udivti3EmbeddedExec

namespace SszX86.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- CALL has one eight-byte store below the 56-byte division activation. -/
def callState (s : MachineData) (ra : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 8)}
    dmem := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8) 8 ra.toInt}

theorem call_slot_load (m : DataMem) (address ra : BitVec 64) :
    Mem.loadInt (Mem.storeInt m address 8 ra.toInt) address 8 =
      some (Int.ofBytes (wordBytes ra)) := by
  rw [wordBytes, ← registerBytes_eq_uintBytes, ofBytes_toBytes]
  exact BoolCodec.load_store_same m address 8 ra.toInt (by decide)

/-- PC 261 has width six, pushes 267, and branches to the linked helper at 160352. -/
theorem call267_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hm : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (hp : Eventually (step e) P
      (callState s (base + 267).toBitVec, base + 160352)) :
    Eventually (step e) P (s, base + 261) := by
  natdiv_step 69 using hc
  apply Delimited.store_cps
  · simpa using hm
  · simpa [callState, Effects.All, Int64.add_assoc] using hp

/-- PC 783 has width six, pushes 789, and branches to the same actual helper. -/
theorem call789_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hm : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (hp : Eventually (step e) P
      (callState s (base + 789).toBitVec, base + 160352)) :
    Eventually (step e) P (s, base + 783) := by
  natdiv_step 212 using hc
  apply Delimited.store_cps
  · simpa using hm
  · simpa [callState, Effects.All, Int64.add_assoc] using hp

/-- A normalized call summary hides the pushed-state representation from clients. -/
structure CallReturned (s : MachineData) (ra : Int64) (t : MachineState) : Prop where
  pc : t.2 = ra
  quotient : Udivti3.value t.1.regs.rax.toBitVec t.1.regs.rdx.toBitVec =
    Udivti3.numerator s / Udivti3.denominator s
  memory : t.1.dmem = (callState s ra.toBitVec).dmem
  vectors : t.1.zmms = s.zmms
  stack : t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec
  saved : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi →
    r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .rsp →
    t.1.regs.get64 r = s.regs.get64 r

theorem call_returned (s : MachineData) (ra : Int64) (t : MachineState)
    (h : Udivti3.Returned (callState s ra.toBitVec) ra.toBitVec t) :
    CallReturned s ra t := by
  refine ⟨?_, h.quotient, h.memory, h.vectors, ?_, ?_⟩
  · simpa only [Int64.ofBitVec_toBitVec] using h.pc
  · have stack := h.stack
    change t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8#64 + 8#64 at stack
    simpa only [BitVec.sub_add_cancel] using stack
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    have saved := h.saved r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    cases r <;> simp_all [callState, Reg64s.get64]

/-- Raw divider continuation for the scalar call site, with all ABI facts intact. -/
theorem udiv267_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (hdiv : Udivti3.Embedded.CodeAt e (base + 160352))
    (s : MachineData) (hd : 0 < Udivti3.denominator s)
    (hm : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (P : MachineState → Prop)
    (hp : ∀ t, Udivti3.Returned (callState s (base + 267).toBitVec)
      (base + 267).toBitVec t → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 261) := by
  apply call267_cps e base hc s P hm
  apply eventually_trans (step e)
    (Udivti3.Returned (callState s (base + 267).toBitVec) (base + 267).toBitVec) P _
  · apply Udivti3.Embedded.program_correct e (base + 160352) hdiv
      (callState s (base + 267).toBitVec) (base + 267).toBitVec hd
    exact call_slot_load s.dmem (s.regs.rsp.toBitVec - 8) (base + 267).toBitVec
  · exact hp

/-- Raw divider continuation for the reverse loop call site. -/
theorem udiv789_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (hdiv : Udivti3.Embedded.CodeAt e (base + 160352))
    (s : MachineData) (hd : 0 < Udivti3.denominator s)
    (hm : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (P : MachineState → Prop)
    (hp : ∀ t, Udivti3.Returned (callState s (base + 789).toBitVec)
      (base + 789).toBitVec t → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 783) := by
  apply call789_cps e base hc s P hm
  apply eventually_trans (step e)
    (Udivti3.Returned (callState s (base + 789).toBitVec) (base + 789).toBitVec) P _
  · apply Udivti3.Embedded.program_correct e (base + 160352) hdiv
      (callState s (base + 789).toBitVec) (base + 789).toBitVec hd
    exact call_slot_load s.dmem (s.regs.rsp.toBitVec - 8) (base + 789).toBitVec
  · exact hp

/-- This CALL composes the structural embedding with the complete checked divider. -/
theorem divide267_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (hdiv : Udivti3.Embedded.CodeAt e (base + 160352))
    (s : MachineData) (hd : 0 < Udivti3.denominator s)
    (hm : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (P : MachineState → Prop)
    (hp : ∀ t, CallReturned s (base + 267) t → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 261) := by
  apply udiv267_cps e base hc hdiv s hd hm P
  intro t h
  exact hp t (call_returned s (base + 267) t h)

/-- The loop CALL uses the same body theorem, including its real RET to PC 789. -/
theorem divide789_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (hdiv : Udivti3.Embedded.CodeAt e (base + 160352))
    (s : MachineData) (hd : 0 < Udivti3.denominator s)
    (hm : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (P : MachineState → Prop)
    (hp : ∀ t, CallReturned s (base + 789) t → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 783) := by
  apply udiv789_cps e base hc hdiv s hd hm P
  intro t h
  exact hp t (call_returned s (base + 789) t h)

/-- The complete helper execution adds no writes beyond CALL's return word. -/
theorem call_frame (s : MachineData) (ra : BitVec 64) (a : BitVec 64)
    (outside : ∀ i < 8, a ≠ (s.regs.rsp.toBitVec - 8) + BitVec.ofNat 64 i) :
    (callState s ra).dmem.get? a = s.dmem.get? a := by
  apply memmove_store_lookup_outside
  intro i hi
  exact outside i (by simpa only [Int.toBytes_length] using hi)

theorem call_mapped (s : MachineData) (ra p : BitVec 64) (count : Nat)
    (hm : UintCodec.Large.Mapped s.dmem p count) :
    UintCodec.Large.Mapped (callState s ra).dmem p count := by
  exact UintCodec.Large.mapped_store _ _ _ _ _ _ hm

/-- The CALL return slot is disjoint from scratch, all saves, and incoming RET. -/
theorem call_local_load (m : DataMem) (sp : BitVec 64) (distance : Nat) (value : Int)
    (within : distance + 8 ≤ 64) :
    Mem.loadInt (Mem.storeInt m (sp - 8) 8 value) (sp + BitVec.ofNat 64 distance) 8 =
      Mem.loadInt m (sp + BitVec.ofNat 64 distance) 8 := by
  apply BoolCodec.load_store_disjoint
  intro i hi j hj
  bv_omega

theorem call_saved (s original : MachineData) (ra : BitVec 64)
    (saved : SavedAt s.dmem s.regs.rsp.toBitVec original) :
    SavedAt (callState s ra).dmem s.regs.rsp.toBitVec original := by
  constructor
  · simpa (disch := decide) only [callState, call_local_load] using saved.rbx
  · simpa (disch := decide) only [callState, call_local_load] using saved.r12
  · simpa (disch := decide) only [callState, call_local_load] using saved.r13
  · simpa (disch := decide) only [callState, call_local_load] using saved.r14
  · simpa (disch := decide) only [callState, call_local_load] using saved.r15
  · simpa (disch := decide) only [callState, call_local_load] using saved.rbp

end SszX86.NatDivision
