import SszX86.CodecIsFixedControl
import SszX86.CodecIsFixedOwned

namespace SszX86.CodecIsFixed
open BoolCodec UintCodec

def fieldsState (s : MachineData) (pointer : BitVec 64) (count : Nat)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rbx := UInt64.ofBitVec pointer
      rax := UInt64.ofNat (8 * count)
      r14 := UInt64.ofNat (24 * count)}
    status := flags}

private theorem scale_fields (count : Nat) :
    (BitVec.ofNat 64 count <<< 3) + (BitVec.ofNat 64 count <<< 3) * 2 =
      BitVec.ofNat 64 (24 * count) := by
  rw [BitVec.ofNat_mul]
  bv_omega

/-- The native iterator's byte count is SHL3 followed by LEA3, not a host Nat
multiplication silently substituted for the machine instructions. -/
theorem fields_setup (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer : BitVec 64) (count : Nat) (P : MachineState → Prop)
    (pointerLoad : Mem.loadInt s.dmem
      (s.regs.rdi.toBitVec + s.regs.rax.toBitVec) 8 = some (pointer.toNat : Int))
    (countLoad : Mem.loadInt s.dmem
      (s.regs.rdi.toBitVec + s.regs.rax.toBitVec + 8) 8 = some (count : Int))
    (next : ∀ flags, Eventually (step e) P (fieldsState s pointer count flags, base + 96)) :
    Eventually (step e) P (s, base + 73) := by
  codec_is_fixed_step 25 using hc
  codec_is_fixed_load pointerLoad
  codec_is_fixed_step 26 using hc
  simp only [MachineData.load, Effects.All, countLoad,
    show Width.W64.bytes = 8 by rfl, show Width.W64.bits = 64 by rfl,
    BitVec.ofInt_ofNat]
  codec_is_fixed_step 27 using hc
  simp (config := {instances := true}) [ShiftCountExpr.interpMasked, ShiftCountExpr.interp,
    ConstExpr.interp, BitVec.take, Effects.All]
  constructor <;> constructor
  all_goals
    codec_is_fixed_step 28 using hc
    codec_is_fixed_step 29 using hc
    have shift : BitVec.ofNat 64 count <<< 3 = BitVec.ofNat 64 (8 * count) := by
      rw [BitVec.ofNat_mul]
      bv_omega
    simpa [fieldsState, scale_fields, shift, UInt64.ofNat, StatusFlags.from_result,
      Effects.All] using next _

theorem container_offset (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with rax := 8}}, base + 73)) :
    Eventually (step e) P (s, base + 68) := by
  codec_is_fixed_step 24 using hc
  exact next

theorem progressive_offset (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with rax := 24}}, base + 73)) :
    Eventually (step e) P (s, base + 61) := by
  codec_is_fixed_step 22 using hc
  codec_is_fixed_step 23 using hc
  exact next

theorem fields_guard (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.r14.toBitVec = 0 then base + 51 else base + 101)) :
    Eventually (step e) P (s, base + 96) := by
  have target := hc.targets ("codec_is_fixed_u51", 51) (by decide)
  codec_is_fixed_step 30 using hc
  constructor <;> codec_is_fixed_step 31 using hc
  all_goals
    by_cases empty : s.regs.r14.toBitVec = 0
    · simpa [StatusFlags.from_result, empty, target, Effects.All] using next _
    · simpa [StatusFlags.from_result, empty, Effects.All] using next _

def childState (s : MachineData) (pointer : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rdi := UInt64.ofBitVec pointer
      rbx := UInt64.ofBitVec (s.regs.rbx.toBitVec + 24)}
    status := flags}

theorem child_prepare (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer : BitVec 64) (P : MachineState → Prop)
    (loaded : Mem.loadInt s.dmem (s.regs.rbx.toBitVec + 16) 8 = some (pointer.toNat : Int))
    (next : ∀ flags, Eventually (step e) P (childState s pointer flags, base + 109)) :
    Eventually (step e) P (s, base + 101) := by
  codec_is_fixed_step 32 using hc
  codec_is_fixed_load loaded
  codec_is_fixed_step 33 using hc
  simpa [childState] using next _

def callState (s : MachineData) (ra : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 8)}
    dmem := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8) 8 ra.toInt}

/-- The sole self-call writes its real return address, PC114, before fetching
original PC0 again. Its continuation is discharged by structural recursion. -/
theorem call_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hm : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (next : Eventually (step e) P (callState s (base + 114).toBitVec, base)) :
    Eventually (step e) P (s, base + 109) := by
  codec_is_fixed_step 34 using hc
  apply Delimited.store_cps
  · simpa using hm
  · simpa [callState, Effects.All, Int64.add_assoc] using next

def decremented (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with r14 := UInt64.ofBitVec (s.regs.r14.toBitVec - 24)}
    status := flags}

theorem child_continue (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (decremented s flags,
        if s.regs.rax.toBitVec.setWidth 8 = 0 then base + 122 else base + 96)) :
    Eventually (step e) P (s, base + 114) := by
  have target := hc.targets ("codec_is_fixed_u96", 96) (by decide)
  codec_is_fixed_step 35 using hc
  codec_is_fixed_step 36 using hc
  constructor <;> codec_is_fixed_step 37 using hc
  all_goals
    by_cases zero : s.regs.rax.toBitVec.setWidth 8 = 0
    · simpa [decremented, StatusFlags.from_result, zero, Effects.All,
        BitVec.sub_eq_add_neg] using next _
    · simpa [decremented, StatusFlags.from_result, zero, target, Effects.All,
        BitVec.sub_eq_add_neg] using next _

end SszX86.CodecIsFixed
