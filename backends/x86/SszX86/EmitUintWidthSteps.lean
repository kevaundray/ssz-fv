import SszX86.EmitUintModel
import SszX86.UintLimbExec

namespace SszX86.Emit.Uint
open Kraken.X64.Parser
open BoolCodec UintCodec

/-- The width scan is readonly and changes only these four registers and flags. -/
def widthState (s : MachineData) (a c d si : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec a
      rcx := UInt64.ofBitVec c
      rdx := UInt64.ofBitVec d
      rsi := UInt64.ofBitVec si}
    status := flags}

theorem cast64 (limb : BitVec 64) : BitVec.ofInt 64 (limb.toNat : Int) = limb := by
  bv_omega

theorem sub_zero (a b : BitVec 64) : a - b = 0#64 ↔ a = b := by
  constructor
  · intro equal
    have same := congrArg (fun x : BitVec 64 => x + b) equal
    simpa only [BitVec.sub_add_cancel, BitVec.zero_add] using same
  · rintro rfl
    exact BitVec.sub_self _

macro "emit_uint_load " h:term : tactic => `(tactic|
  (have observed := $h
   try simp only [BitVec.ofNat_eq_ofNat] at observed
   simp only [widthState, UInt64.toBitVec_ofBitVec, MachineData.load,
      Width.bytes, Width.bits, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
      Effects.All]
   rw [observed]
   simp only [Effects.All, cast64]))

/-- Actual value-tag compare and branch; the tag is an original entry fact. -/
theorem width_tag (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (tag : s.regs.rcx.toBitVec = 1#64)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags}, base + 59)) :
    Eventually (step e) P (s, base + 50) := by
  emit_step 17 using hc
  emit_step 18 using hc
  simpa [tag, StatusFlags.from_result, Effects.All] using next _

/-- Both exact descriptor words are loaded before selecting Small/Large. -/
theorem width_header (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload : BitVec 64) (P : MachineState → Prop)
    (hp : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8) 8 = some (pointer.toNat : Int))
    (hv : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16) 8 = some (payload.toNat : Int))
    (next : ∀ flags, Eventually (step e) P
      (widthState s pointer s.regs.rcx.toBitVec s.regs.rdx.toBitVec payload flags,
        if pointer = 0#64 then base + 583 else base + 76)) :
    Eventually (step e) P (s, base + 59) := by
  have target := hc.targets ("emit_u583", 583) (by decide)
  emit_step 19 using hc
  emit_uint_load hp
  emit_step 20 using hc
  emit_uint_load hv
  emit_step 21 using hc
  constructor <;> emit_step 22 using hc
  all_goals
    by_cases zero : pointer = 0#64
    · simpa [widthState, target, zero, StatusFlags.from_result, Effects.All] using next _
    · simpa [widthState, zero, StatusFlags.from_result, Effects.All] using next _

/-- Initial LEA forms count+1; physical limb bounds make this nonwrapping. -/
theorem width_begin (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c d si : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      (widthState s a (si + 1) d si flags, base + 80)) :
    Eventually (step e) P (widthState s a c d si flags, base + 76) := by
  emit_step 23 using hc
  simpa [widthState, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.add_comm] using next

/-- The actual empty-count edge, including Large [] and an all-zero scan. -/
theorem width_scan_empty (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a d si : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (widthState s a 1 d si flags, base + 575)) :
    Eventually (step e) P (widthState s a 1 d si flags, base + 80) := by
  have target := hc.targets ("emit_u575", 575) (by decide)
  emit_step 24 using hc
  emit_step 25 using hc
  simpa [widthState, target, StatusFlags.from_result, Effects.All] using next _

/-- One high-zero countdown iteration. The limb read is the original physical
limb, and the real backward conditional jump is part of the certificate. -/
theorem width_scan_zero_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a d si : BitVec 64) (flags : StatusFlags)
    (n : Nat) (positive : 0 < n) (bound : n + 1 < 2 ^ 64)
    (zero : Mem.loadInt s.dmem (a + BitVec.ofNat 64 (8 * (n - 1))) 8 = some 0)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (widthState s a (BitVec.ofNat 64 n) (BitVec.ofNat 64 n) si flags, base + 80)) :
    Eventually (step e) P
      (widthState s a (BitVec.ofNat 64 (n + 1)) d si flags, base + 80) := by
  have target := hc.targets ("emit_u80", 80) (by decide)
  have nonempty : BitVec.ofNat 64 (n + 1) ≠ 1#64 := by
    intro equal
    have value := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at value
    omega
  have branch : (BitVec.ofNat 64 (n + 1) - 1#64 == BitVec.zero 64) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro equal
    exact nonempty ((sub_zero (BitVec.ofNat 64 (n + 1)) 1#64).mp equal)
  have minus : BitVec.ofNat 64 (n + 1) + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 n := by
    bv_omega
  have address : a + BitVec.ofNat 64 (n + 1) * 8#64 + 18446744073709551600#64 =
      a + BitVec.ofNat 64 (8 * (n - 1)) := by
    bv_omega
  emit_step 24 using hc
  emit_step 25 using hc
  simp only [widthState, UInt64.toBitVec_ofBitVec, StatusFlags.from_result]
  rw [branch]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  emit_step 26 using hc
  emit_step 27 using hc
  simp only [MachineData.load, Width.bytes, Effects.All]
  rw [address, zero]
  simp only [Effects.All, Width.bits]
  emit_step 28 using hc
  emit_step 29 using hc
  change Eventually (step e) P
    (widthState s a
      (BitVec.ofNat 64 (n + 1) + BitVec.ofInt 64 (-1))
      (BitVec.ofNat 64 (n + 1) + BitVec.ofInt 64 (-1)) si
      (StatusFlags.from_result 0#64 {cf := false, af := false, of := false}),
      e.labels.label "emit_u80")
  rw [minus, target]
  exact next _

/-- The sole nonzero significant limb takes the actual width-load edge. -/
theorem width_scan_one (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a d si limb : BitVec 64) (flags : StatusFlags)
    (nonzero : limb ≠ 0#64)
    (stored : Mem.loadInt s.dmem a 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (widthState s a 1 1 si flags, base + 580)) :
    Eventually (step e) P (widthState s a 2 d si flags, base + 80) := by
  have target := hc.targets ("emit_u580", 580) (by decide)
  have address : a + 16#64 + 18446744073709551600#64 = a := by bv_omega
  emit_step 24 using hc
  emit_step 25 using hc
  simp [widthState, StatusFlags.from_result, Effects.All]
  emit_step 26 using hc
  emit_step 27 using hc
  simp only [MachineData.load, Width.bytes, Effects.All]
  rw [address, stored]
  simp only [Effects.All, Width.bits, cast64]
  emit_step 28 using hc
  emit_step 29 using hc
  simp [StatusFlags.from_result, nonzero, Effects.All]
  emit_step 30 using hc
  emit_step 31 using hc
  simpa [widthState, target, StatusFlags.from_result, Effects.All] using next _

/-- The zero-count path still distinguishes physical Large [] from a padded
zero, because the latter performs the real low-limb load. -/
theorem width_scan_finish (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c d si : BitVec 64) (flags : StatusFlags)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (widthState s a c d si flags, if si = 0#64 then base + 653 else base + 580)) :
    Eventually (step e) P (widthState s a c d si flags, base + 575) := by
  have target := hc.targets ("emit_u653", 653) (by decide)
  emit_step 112 using hc
  constructor <;> emit_step 113 using hc
  all_goals
    by_cases empty : si = 0#64
    · simpa [widthState, empty, target, StatusFlags.from_result, Effects.All] using next _
    · simpa [widthState, empty, StatusFlags.from_result, Effects.All] using next _

/-- The normalized word is obtained from the original readonly allocation. -/
theorem width_low_load (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a c d si limb : BitVec 64) (flags : StatusFlags)
    (stored : Mem.loadInt s.dmem a 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (widthState s a c d limb flags, base + 583)) :
    Eventually (step e) P (widthState s a c d si flags, base + 580) := by
  emit_step 114 using hc
  emit_uint_load stored
  simpa [widthState] using next

end SszX86.Emit.Uint
