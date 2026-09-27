import SszX86.NatDivisionSmall
import SszX86.NatDivisionCall

namespace SszX86.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Only the small-result representation fields change after a zero high
quotient limb; RAX remains available for the low-product remainder recovery. -/
def narrowState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rcx := s.regs.rax, rdi := 0}, status := flags}

theorem quotient_dispatch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.rdx.toBitVec = 0 → ∀ flags, Eventually (step e) P
      (narrowState s flags, base + 358))
    (large : s.regs.rdx.toBitVec ≠ 0 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 279)) :
    Eventually (step e) P (s, base + 267) := by
  have target := hc.targets ("natDivision_u279", 279) (by decide)
  natdiv_step 70 using hc
  constructor <;> natdiv_step 71 using hc
  all_goals
    by_cases hz : s.regs.rdx.toBitVec = 0#64
    · simp [StatusFlags.from_result, hz, Effects.All]
      natdiv_step 72 using hc
      natdiv_step 73 using hc
      constructor <;> natdiv_step 74 using hc
      all_goals simpa [narrowState] using small hz _
    · simpa [StatusFlags.from_result, hz, target, Effects.All] using large hz _

structure Divided (s : MachineData) (ra : Int64) (t : MachineState) : Prop where
  pc : t.2 = ra
  quotient : Udivti3.value t.1.regs.rax.toBitVec t.1.regs.rdx.toBitVec =
    Udivti3.value s.regs.r15.toBitVec s.regs.rsi.toBitVec / s.regs.r13.toBitVec.toNat
  memory : t.1.dmem = (callState s ra.toBitVec).dmem
  vectors : t.1.zmms = s.zmms
  stack : t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec
  output : t.1.regs.rbx = s.regs.rbx
  arena : t.1.regs.r12 = s.regs.r12
  divisor : t.1.regs.r13 = s.regs.r13
  reason : t.1.regs.r14 = 0
  low : t.1.regs.r15 = s.regs.r15
  base_pointer : t.1.regs.rbp = s.regs.rbp

/-- The actual argument setup, six-byte CALL, complete embedded divider, and
callee RET are composed before inspecting either quotient word. -/
theorem wide_call_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (hdiv : Udivti3.Embedded.CodeAt e (base + 160352))
    (s : MachineData) (hd : 0 < s.regs.r13.toBitVec.toNat)
    (hm : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (P : MachineState → Prop)
    (hp : ∀ t, Divided s (base + 267) t → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 250) := by
  apply arguments_cps e base hc s P
  intro flags
  apply divide267_cps e base hc hdiv (arguments s flags)
  · simpa [arguments, Udivti3.denominator, Udivti3.value] using hd
  · exact hm
  intro t h
  apply hp t
  refine ⟨h.pc, ?_, h.memory, h.vectors, h.stack, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [arguments, Udivti3.numerator, Udivti3.denominator, Udivti3.value] using h.quotient
  all_goals
    apply UInt64.toBitVec_inj.mp
    first
    | exact h.saved .rbx (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
    | exact h.saved .r12 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
    | exact h.saved .r13 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
    | exact h.saved .r14 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
    | exact h.saved .r15 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
    | exact h.saved .rbp (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)

end SszX86.NatDivision
