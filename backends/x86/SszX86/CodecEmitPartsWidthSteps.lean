import SszX86.CodecEmitPartsSteps
import SszX86.EmitUintWidth

namespace SszX86.CodecEmitParts
open UintCodec

/-- Actual readonly scratch registers of the inlined retained-size narrowing.
RCX remains the child Plan pointer throughout the scan. -/
def widthState (s : MachineData) (a count d size : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec a, r11 := UInt64.ofBitVec count,
    rdx := UInt64.ofBitVec d, r9 := UInt64.ofBitVec size}, status := flags}

macro "codec_parts_width_load " observation:term : tactic => `(tactic|
  (have observed := $observation
   try simp only [BitVec.ofNat_eq_ofNat] at observed
   simp only [widthState, UInt64.toBitVec_ofBitVec, MachineData.load,
     Width.bytes, Width.bits, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt, Effects.All]
   rw [observed]
   simp only [Effects.All, Emit.Uint.cast64]))

theorem width_header (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (pointer payload : BitVec 64) (P : MachineState → Prop)
    (hp : Mem.loadInt s.dmem (s.regs.rcx.toBitVec + 16) 8 = some (pointer.toNat : Int))
    (hv : Mem.loadInt s.dmem (s.regs.rcx.toBitVec + 24) 8 = some (payload.toNat : Int))
    (next : ∀ flags, Eventually (step e) P
      (widthState s pointer s.regs.r11.toBitVec s.regs.rdx.toBitVec payload flags,
        if pointer = 0#64 then base + 300 else base + 240)) :
    Eventually (step e) P (s, base + 227) := by
  have target := code.targets ("codec_emit_parts_u300", 300) (by decide)
  codec_parts_step 53 using code
  codec_parts_width_load hp
  codec_parts_step 54 using code
  codec_parts_width_load hv
  codec_parts_step 55 using code
  constructor <;> codec_parts_step 56 using code
  all_goals
    by_cases zero : pointer = 0#64
    · simpa [widthState, target, zero, StatusFlags.from_result, Effects.All] using next _
    · simpa [widthState, zero, StatusFlags.from_result, Effects.All] using next _

/-- The actual encoded ten-byte and two-byte NOPs precede the countdown CMP. -/
theorem width_begin (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (a count d size : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (widthState s a (size + 1) d size flags, base + 256)) :
    Eventually (step e) P (widthState s a count d size flags, base + 240) := by
  codec_parts_step 57 using code
  codec_parts_step 58 using code
  codec_parts_step 59 using code
  simpa [widthState, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.add_comm] using next

theorem width_scan_empty (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (a d size : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (widthState s a 1 d size flags, base + 288)) :
    Eventually (step e) P (widthState s a 1 d size flags, base + 256) := by
  have target := code.targets ("codec_emit_parts_u288", 288) (by decide)
  codec_parts_step 60 using code
  codec_parts_step 61 using code
  simpa [widthState, target, StatusFlags.from_result, Effects.All] using next _

theorem width_scan_zero_step (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (a d size : BitVec 64) (flags : StatusFlags)
    (n : Nat) (positive : 0 < n) (bound : n + 1 < 2 ^ 64)
    (zero : Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8 * (n - 1))) 8 = some 0)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (widthState s a (BitVec.ofNat 64 n) (BitVec.ofNat 64 n) size flags, base + 256)) :
    Eventually (step e) P
      (widthState s a (BitVec.ofNat 64 (n + 1)) d size flags, base + 256) := by
  have target := code.targets ("codec_emit_parts_u256", 256) (by decide)
  have nonempty : BitVec.ofNat 64 (n + 1) ≠ 1#64 := by
    intro equal
    have value := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at value
    omega
  have branch : (BitVec.ofNat 64 (n + 1) - 1#64 == BitVec.zero 64) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro equal
    exact nonempty ((Emit.Uint.sub_zero (BitVec.ofNat 64 (n + 1)) 1#64).mp equal)
  have minus : BitVec.ofNat 64 (n + 1) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 n := by
    bv_omega
  have address : a + BitVec.ofNat 64 (n + 1) * 8#64 + 18446744073709551600#64 =
      a + BitVec.ofNat 64 (8 * (n - 1)) := by bv_omega
  codec_parts_step 60 using code
  codec_parts_step 61 using code
  simp only [widthState, UInt64.toBitVec_ofBitVec, StatusFlags.from_result]
  rw [branch]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  codec_parts_step 62 using code
  codec_parts_step 63 using code
  simp only [MachineData.load, Width.bytes, Effects.All]
  rw [address, zero]
  simp only [Effects.All, Width.bits]
  codec_parts_step 64 using code
  codec_parts_step 65 using code
  change Eventually (step e) P
    (widthState s a (BitVec.ofNat 64 (n + 1) + BitVec.ofInt 64 (-1))
      (BitVec.ofNat 64 (n + 1) + BitVec.ofInt 64 (-1)) size
      (StatusFlags.from_result 0#64 {cf := false, af := false, of := false}),
      e.labels.label "codec_emit_parts_u256")
  rw [minus, target]
  exact next _

theorem width_scan_one (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (a d size limb : BitVec 64) (flags : StatusFlags)
    (nonzero : limb ≠ 0#64) (stored : Mem.loadInt s.dmem a 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (widthState s a 1 1 size flags, base + 297)) :
    Eventually (step e) P (widthState s a 2 d size flags, base + 256) := by
  have target := code.targets ("codec_emit_parts_u297", 297) (by decide)
  have address : a + 16#64 + 18446744073709551600#64 = a := by bv_omega
  codec_parts_step 60 using code
  codec_parts_step 61 using code
  simp [widthState, StatusFlags.from_result, Effects.All]
  codec_parts_step 62 using code
  codec_parts_step 63 using code
  simp only [MachineData.load, Width.bytes, Effects.All]
  rw [address, stored]
  simp only [Effects.All, Width.bits, Emit.Uint.cast64]
  codec_parts_step 64 using code
  codec_parts_step 65 using code
  simp [StatusFlags.from_result, nonzero, Effects.All]
  codec_parts_step 66 using code
  codec_parts_step 67 using code
  simpa [widthState, target, StatusFlags.from_result, Effects.All] using next _

theorem width_scan_finish (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (a count d size : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (widthState s a count d size flags, if size = 0#64 then base + 436 else base + 297)) :
    Eventually (step e) P (widthState s a count d size flags, base + 288) := by
  have target := code.targets ("codec_emit_parts_u436", 436) (by decide)
  codec_parts_step 69 using code
  constructor <;> codec_parts_step 70 using code
  all_goals
    by_cases empty : size = 0#64
    · simpa [widthState, empty, target, StatusFlags.from_result, Effects.All] using next _
    · simpa [widthState, empty, StatusFlags.from_result, Effects.All] using next _

theorem width_low_load (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (a count d size limb : BitVec 64) (flags : StatusFlags)
    (stored : Mem.loadInt s.dmem a 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (widthState s a count d limb flags, base + 300)) :
    Eventually (step e) P (widthState s a count d size flags, base + 297) := by
  codec_parts_step 71 using code
  codec_parts_width_load stored
  simpa [widthState] using next

end SszX86.CodecEmitParts
