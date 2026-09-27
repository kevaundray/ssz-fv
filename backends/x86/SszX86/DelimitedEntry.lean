import SszX86.DelimitedCore

namespace SszX86.Delimited

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def byteState (s : MachineData) (byte : UInt8) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with rax := UInt64.ofBitVec (byte.toBitVec.setWidth 64)}
    status := flags}

/-- The only read before selecting the framed and unframed nonempty paths is
input[len-1]. The Option discriminant and arena are not inspected here. -/
theorem last_byte_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (byte : UInt8)
    (hl : Mem.loadInt s.dmem (s.regs.rdx.toBitVec + s.regs.rcx.toBitVec - 1#64) 1 =
      some (byte.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (byteState s byte flags, if byte = 0 then base + 233 else base + 22)) :
    Eventually (step e) P (s, base + 9) := by
  have target := hc.targets ("delimited_u233", 233) (by decide)
  have minus : -(1#64) = 18446744073709551615#64 := by decide
  have hl' : Mem.loadInt s.dmem
      (s.regs.rdx.toBitVec + s.regs.rcx.toBitVec + 18446744073709551615#64) 1 =
        some (byte.toNat : Int) := by
    simpa only [BitVec.sub_eq_add_neg, minus] using hl
  delimited_step 2 using hc
  delimited_load hl'
  delimited_step 3 using hc
  constructor <;> delimited_step 4 using hc
  all_goals
    by_cases zero : byte = 0
    · simpa [zero, target, byteState, StatusFlags.from_result, Effects.All] using hp _
    · have nonzero : byte.toBitVec ≠ 0#8 := by
        intro he
        apply zero
        exact UInt8.toBitVec_inj.1 he
      simpa [zero, nonzero, byteState, StatusFlags.from_result, Effects.All] using hp _

/-- The alignment NOP occupies its real five bytes and has no effects. -/
theorem scan_init_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rax := 0}, status := flags}, base + 240)) :
    Eventually (step e) P (s, base + 233) := by
  delimited_step 53 using hc
  constructor <;> delimited_step 54 using hc
  all_goals exact hp _

theorem no_delimiter_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : Eventually (step e) P ({s with regs := {s.regs with rax := 17}}, base + 587)) :
    Eventually (step e) P (s, base + 582) := by
  delimited_step 137 using hc
  exact hp

theorem trailing_zeros_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : Eventually (step e) P ({s with regs := {s.regs with rax := 18}}, base + 587)) :
    Eventually (step e) P (s, base + 259) := by
  delimited_step 60 using hc
  delimited_step 61 using hc
  exact hp

end SszX86.Delimited
