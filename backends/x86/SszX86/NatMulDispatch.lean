import SszX86.NatMulScanLeft
import SszX86.NatMulScanRight
import SszX86.NatAddControl

namespace SszX86.NatMul

abbrev ControlFrame := NatAdd.ControlFrame

def payloadState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := s.regs.rdx}, status := flags}

theorem left_entry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.rsi.toBitVec = 0#64 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 63))
    (large : s.regs.rsi.toBitVec ≠ 0#64 → ∀ flags, Eventually (step e) P
      (leftScanState s s.regs.r10.toBitVec (s.regs.rdx.toBitVec + 1) flags, base + 32)) :
    Eventually (step e) P (s, base + 14) := by
  have target := hc.targets ("natMul_u63", 63) (by decide)
  natmul_step 0 row 7 using hc
  constructor <;> natmul_step 0 row 8 using hc
  all_goals
    by_cases zero : s.regs.rsi.toBitVec = 0#64
    · simpa [StatusFlags.from_result, zero, target, Effects.All] using small zero _
    · simp [StatusFlags.from_result, zero, Effects.All]
      natmul_step 0 row 9 using hc
      natmul_step 0 row 10 using hc
      simpa [leftScanState, BitVec.ofInt_add, BitVec.ofInt_toInt, UInt64.add_comm] using large zero _

theorem scanned_left_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.rcx.toBitVec = 0#64 → ∀ flags, Eventually (step e) P
      (payloadState s flags, base + 100))
    (large : s.regs.rcx.toBitVec ≠ 0#64 → ∀ flags, Eventually (step e) P
      (payloadState s flags, base + 129)) :
    Eventually (step e) P (s, base + 53) := by
  have target := hc.targets ("natMul_u129", 129) (by decide)
  natmul_step 0 row 17 using hc
  natmul_step 0 row 18 using hc
  constructor <;> natmul_step 0 row 19 using hc
  all_goals
    by_cases zero : s.regs.rcx.toBitVec = 0#64
    · simp [StatusFlags.from_result, zero, Effects.All]
      natmul_step 0 row 20 using hc
      simpa [payloadState] using small zero _
    · simpa [StatusFlags.from_result, zero, target, payloadState, Effects.All] using large zero _

theorem zero_left_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.rcx.toBitVec = 0#64 → ∀ flags, Eventually (step e) P
      ({payloadState s flags with regs := {(payloadState s flags).regs with r12 := 0}}, base + 100))
    (large : s.regs.rcx.toBitVec ≠ 0#64 → ∀ flags, Eventually (step e) P
      ({payloadState s flags with regs := {(payloadState s flags).regs with r12 := 0}}, base + 129)) :
    Eventually (step e) P (s, base + 89) := by
  have target := hc.targets ("natMul_u129", 129) (by decide)
  natmul_step 0 row 30 using hc
  constructor <;> natmul_step 0 row 31 using hc
  all_goals
    natmul_step 1 row 0 using hc
    constructor <;> natmul_step 1 row 1 using hc
    all_goals
      by_cases zero : s.regs.rcx.toBitVec = 0#64
      · simpa [StatusFlags.from_result, zero, payloadState, Effects.All] using small zero _
      · simpa [StatusFlags.from_result, zero, target, payloadState, Effects.All] using large zero _

theorem right_entry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (rightScanState s (-s.regs.r8.toBitVec) (s.regs.r8.toBitVec + 1) s.regs.r13.toBitVec flags,
        base + 144)) :
    Eventually (step e) P (s, base + 129) := by
  natmul_step 1 row 13 using hc
  natmul_step 1 row 14 using hc
  natmul_step 1 row 15 using hc
  natmul_step 1 row 16 using hc
  simpa [rightScanState, BitVec.ofInt_add, BitVec.ofInt_toInt, UInt64.add_comm] using next _

def factorState (s : MachineData) : MachineData :=
  {s with regs := {s.regs with rcx := s.regs.r8}}

theorem right_factor_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (factorState s, base + 184)) :
    Eventually (step e) P (s, base + 181) := by
  natmul_step 1 row 29 using hc
  exact next

def helperArenaState (s : MachineData) : MachineData :=
  {s with regs := {s.regs with r8 := s.regs.r9}}

theorem helper_arena_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (helperArenaState s, base + 187)) :
    Eventually (step e) P (s, base + 184) := by
  natmul_step 1 row 30 using hc
  exact next

def swappedState (s : MachineData) : MachineData :=
  {s with regs := {s.regs with rsi := s.regs.rcx, rdx := s.regs.r8, rcx := s.regs.rax}}

theorem swapped_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (swappedState s, base + 184)) :
    Eventually (step e) P (s, base + 709) := by
  natmul_step 6 row 7 using hc
  natmul_step 6 row 8 using hc
  natmul_step 6 row 9 using hc
  natmul_step 6 row 10 using hc
  exact next

end SszX86.NatMul
