import SszX86.NatDivisionLoopExec

namespace SszX86.NatDivision.Loop

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- An iteration exposes only the loop registers and the two real writes.
All runtime-divider caller-clobbered temporaries remain opaque. -/
structure Iteration (s : MachineData) (ra : BitVec 64) (limb : BitVec 64)
    (t : MachineData) : Prop where
  divisor : get t .rbx = get s .rbx
  count : get t .r13 = get s .r13
  destination : get t .r14 = get s .r14
  stack : get t .rsp = get s .rsp
  index : get t .rbp = get s .rbp - 8#64
  remainder : get t .r15 = BitVec.ofNat 64
    (SszNative.LimbDivision.step (get s .rbx) (get s .r15).toNat limb).2
  memory : t.dmem = Mem.storeInt
    (Mem.storeInt s.dmem (get s .rsp - 8#64) 8 ra.toInt)
    (get s .r14 + get s .rbp) 8
    (SszNative.LimbDivision.step (get s .rbx) (get s .r15).toNat limb).1.toInt
  vectors : t.zmms = s.zmms

/-- One complete execution, including the actual CALL at 783, the helper's
real RET, quotient store, MUL/SUB, and conditional back edge. -/
theorem iteration_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (hdiv : Udivti3.Embedded.CodeAt e (base + 160352))
    (s : MachineData) (limb : BitVec 64)
    (hr : (get s .r15).toNat < (get s .rbx).toNat)
    (loaded : Mem.loadInt s.dmem (get s .r14 + get s .rbp) 8 = some (limb.toNat : Int))
    (slot : ∃ old, Mem.loadInt s.dmem (get s .rsp - 8#64) 8 = some old)
    (apart : ∀ i < 8, ∀ j < 8,
      get s .r14 + get s .rbp + BitVec.ofNat 64 i ≠
        get s .rsp - 8#64 + BitVec.ofNat 64 j)
    (P : MachineState → Prop)
    (next : ∀ t, Iteration s (base + 789).toBitVec limb t →
      Eventually (step e) P (t, if get s .rbp = 0 then base + 477 else base + 768)) :
    Eventually (step e) P (s, base + 768) := by
  apply arguments_cps e base hc s limb loaded P
  intro flags
  apply divide789_cps e base hc hdiv (arguments s limb flags)
  · have hd : 0 < (get s .rbx).toNat := Nat.zero_lt_of_lt hr
    simpa [arguments, Udivti3.denominator, Udivti3.value, get, Reg64s.get64] using hd
  · exact slot
  intro returned hreturned
  have hb := hreturned.saved .rbx (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hn := hreturned.saved .r13 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp := hreturned.saved .r14 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hi := hreturned.saved .rbp (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hw := hreturned.saved .r12 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [arguments, Reg64s.get64, UInt64.toBitVec_ofBitVec] at hb hn hp hi hw
  have hq : Udivti3.value (get returned.1 .rax) (get returned.1 .rdx) =
      Udivti3.value limb (get s .r15) / (get s .rbx).toNat := by
    simpa [get, Reg64s.get64, Udivti3.numerator, Udivti3.denominator,
      Udivti3.value, Udivti3.radix, arguments] using hreturned.quotient
  have quotient := (loop_quotient limb (get s .r15) (get s .rbx)
    (get returned.1 .rax) (get returned.1 .rdx) hr hq).2
  have remainder := loop_remainder limb (get s .r15) (get s .rbx)
    (get returned.1 .rax) (get returned.1 .rdx) hq
  rcases returned with ⟨t, pc⟩
  dsimp only [Prod.fst, Prod.snd] at *
  have pcReturned : pc = base + 789 := hreturned.pc
  have memory : t.dmem =
      Mem.storeInt s.dmem (get s .rsp - 8#64) 8 (base + 789).toBitVec.toInt := hreturned.memory
  have destination : get t .r14 = get s .r14 := hp
  have index : get t .rbp = get s .rbp := hi
  rw [pcReturned]
  apply tail_cps e base hc t
  · rw [memory, destination, index, BoolCodec.load_store_disjoint _ _ _ 8 8 _ apart]
    exact ⟨_, loaded⟩
  intro tailFlags
  apply advance_cps e base hc
  intro finalFlags
  have result : Iteration s (base + 789).toBitVec limb
      (advance (tailState t tailFlags) finalFlags) := by
    constructor
    · simpa [advance, tailState, get, Reg64s.get64] using hb
    · simpa [advance, tailState, get, Reg64s.get64] using hn
    · simpa [advance, tailState, get, Reg64s.get64] using hp
    · simpa [advance, tailState, get, Reg64s.get64, arguments] using hreturned.stack
    · simp [advance, tailState, get, Reg64s.get64, hi]
    · simpa [advance, tailState, get, Reg64s.get64, hw, hb] using remainder
    · change Mem.storeInt t.dmem (get t .r14 + get t .rbp) 8 (get t .rax).toInt = _
      rw [memory, destination, index, quotient]
    · exact hreturned.vectors
  have indexTail : get (tailState t tailFlags) .rbp = get s .rbp := hi
  change Eventually (step e) P
    (advance (tailState t tailFlags) finalFlags,
      if get (tailState t tailFlags) .rbp = 0#64 then base + 477 else base + 768)
  rw [indexTail]
  exact next _ result

end SszX86.NatDivision.Loop
