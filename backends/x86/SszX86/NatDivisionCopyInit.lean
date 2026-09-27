import SszX86.NatDivisionCopyTail

namespace SszX86.NatDivision.Copy
open Kraken.X64.Parser

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def initPair (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r8 := UInt64.ofBitVec (get s .r8 + 1#64)
      rcx := UInt64.ofBitVec (get s .rcx &&& get s .rax)
      r9 := UInt64.ofBitVec (get s .r9 + 8#64)
      r10 := 0}
    status := flags}

def initSingle (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r8 := 0
      r14 := UInt64.ofBitVec (get s .r14 + get s .rdi)}
    status := flags}

/-- INC and its length comparison select the scalar or the two-word copy. -/
theorem init_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (single : get s .rdx = get s .r8 + 1#64 → ∀ flags,
      Eventually (step e) P (initSingle s flags, base + 736))
    (pairs : get s .rdx ≠ get s .r8 + 1#64 → ∀ flags,
      Eventually (step e) P (initPair s flags, base + 669)) :
    Eventually (step e) P (s, base + 627) := by
  have target640 := hc.targets ("natDivision_u640", 640) (by decide)
  natdiv_step 161 using hc
  natdiv_step 162 using hc
  natdiv_step 163 using hc
  by_cases one : s.regs.rdx.toBitVec = s.regs.r8.toBitVec + 1#64
  · simp [StatusFlags.from_result, one]
    natdiv_step 164 using hc
    constructor <;> natdiv_step 165 using hc
    all_goals natdiv_step 195 using hc
    all_goals simpa [initSingle, get, Reg64s.get64, UInt64.add_comm] using single one _
  · simp [StatusFlags.from_result, one, target640]
    natdiv_step 166 using hc
    constructor <;> natdiv_step 167 using hc
    all_goals natdiv_step 168 using hc
    all_goals constructor <;> natdiv_step 169 using hc
    all_goals simpa [initPair, get, Reg64s.get64, UInt64.add_comm, UInt64.and_comm] using pairs one _

end SszX86.NatDivision.Copy
