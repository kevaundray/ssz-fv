import SszX86.EmitBitsMemory

namespace SszX86.Emit.Bits
open BoolCodec UintCodec
open BitVector (constructLow constructHigh constructQuotient)

/-- Only the descriptor tag is inspected at the bit body dispatch. -/
theorem route_list (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (tag : Nat) (validTag : tag = 5 ∨ tag = 6)
    (stored : s.regs.rax.toBitVec = BitVec.ofNat 64 tag) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rcx := UInt64.ofNat (tag - 5)}, status := flags}, base + 428)) :
    Eventually (step e) P (s, base + 414) := by
  rcases validTag with rfl | rfl
  · have lea : s.regs.rax + (18446744073709551611 : UInt64) = 0 := by
      apply UInt64.toBitVec_inj.mp
      change s.regs.rax.toBitVec + 18446744073709551611#64 = 0#64
      rw [stored]
      decide
    emit_step 69 using hc
    rw [lea]
    change Eventually (step e) P ({s with regs := {s.regs with rcx := 0}}, base + 418)
    emit_step 70 using hc
    emit_step 71 using hc
    change Eventually (step e) P ({s with regs := {s.regs with rcx := 0}, status := _}, base + 428)
    exact next _
  · have lea : s.regs.rax + (18446744073709551611 : UInt64) = 1 := by
      apply UInt64.toBitVec_inj.mp
      change s.regs.rax.toBitVec + 18446744073709551611#64 = 1#64
      rw [stored]
      decide
    emit_step 69 using hc
    rw [lea]
    change Eventually (step e) P ({s with regs := {s.regs with rcx := 1}}, base + 418)
    emit_step 70 using hc
    emit_step 71 using hc
    change Eventually (step e) P ({s with regs := {s.regs with rcx := 1}, status := _}, base + 428)
    exact next _

theorem route_vector (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (stored : s.regs.rax.toBitVec = 4#64) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rcx := 18446744073709551615}, status := flags}, base + 672)) :
    Eventually (step e) P (s, base + 414) := by
  have target := hc.targets ("emit_u663", 663) (by decide)
  have lea : s.regs.rax + (18446744073709551611 : UInt64) = 18446744073709551615 := by
    apply UInt64.toBitVec_inj.mp
    change s.regs.rax.toBitVec + 18446744073709551611#64 = 18446744073709551615#64
    rw [stored]
    decide
  emit_step 69 using hc
  rw [lea]
  change Eventually (step e) P
    ({s with regs := {s.regs with rcx := 18446744073709551615}}, base + 418)
  emit_step 70 using hc
  emit_step 71 using hc
  change Eventually (step e) P
    ({s with regs := {s.regs with rcx := 18446744073709551615}, status := _}, e.labels.label "emit_u663")
  rw [target]
  emit_step 135 using hc
  simp only [stored]
  emit_step 136 using hc
  change Eventually (step e) P
    ({s with regs := {s.regs with rcx := 18446744073709551615}, status := _}, base + 672)
  exact next _

def countLoaded (s : MachineData) (count : BitVec 128) : MachineData :=
  {s with regs := {s.regs with
    rax := UInt64.ofBitVec (constructLow count)
    r13 := UInt64.ofBitVec (constructHigh count)}}

theorem load_count (e : Executable) (base : Int64) (hc : CodeAt e base)
    (list : Bool) (s : MachineData) (count : BitVec 128)
    (low : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 32) 8 =
      some ((constructLow count).toNat : Int))
    (high : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 40) 8 =
      some ((constructHigh count).toNat : Int)) (P : MachineState → Prop)
    (next : Eventually (step e) P (countLoaded s count, base + if list then 438 else 682)) :
    Eventually (step e) P (s, base + if list then 428 else 672) := by
  change Mem.loadInt s.dmem (s.regs.r12.toBitVec + 32#64) 8 =
    some ((constructLow count).toNat : Int) at low
  change Mem.loadInt s.dmem (s.regs.r12.toBitVec + 40#64) 8 =
    some ((constructHigh count).toNat : Int) at high
  have lowBits : BitVec.ofInt 64 ((constructLow count).toNat : Int) = constructLow count := by
    simp only [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have highBits : BitVec.ofInt 64 ((constructHigh count).toNat : Int) = constructHigh count := by
    simp only [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  change BitVec.ofInt 64 ((count.toNat : Int) % 18446744073709551616) =
    constructLow count at lowBits
  cases list
  · emit_step 137 using hc
    simp only [MachineData.load]
    rw [low]
    simp only [Effects.All]
    emit_step 138 using hc
    simp only [MachineData.load]
    rw [high]
    simpa only [Effects.All, countLoaded, lowBits, Width.bits, highBits, Bool.false_eq_true, ↓reduceIte] using next
  · emit_step 72 using hc
    simp only [MachineData.load]
    rw [low]
    simp only [Effects.All]
    emit_step 73 using hc
    simp only [MachineData.load]
    rw [high]
    simpa only [Effects.All, countLoaded, lowBits, Width.bits, highBits, ↓reduceIte] using next

def quotientState (s : MachineData) (count : BitVec 128) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with r13 := UInt64.ofBitVec (constructQuotient count)}, status := flags}

theorem shift_count (e : Executable) (base : Int64) (hc : CodeAt e base)
    (list : Bool) (s : MachineData) (count : BitVec 128)
    (low : s.regs.rax.toBitVec = constructLow count)
    (high : s.regs.r13.toBitVec = constructHigh count) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (quotientState s count flags, base + if list then 443 else 687)) :
    Eventually (step e) P (s, base + if list then 438 else 682) := by
  cases list
  · emit_step 139 using hc
    simp (config := {instances := true}) [ShiftCountExpr.interpMasked, ShiftCountExpr.interp,
      ConstExpr.interp, BitVec.take, Effects.All]
    constructor <;> constructor
    all_goals simpa [low, high, quotientState, constructQuotient, StatusFlags.from_result,
      Effects.All] using next _
  · emit_step 74 using hc
    simp (config := {instances := true}) [ShiftCountExpr.interpMasked, ShiftCountExpr.interp,
      ConstExpr.interp, BitVec.take, Effects.All]
    constructor <;> constructor
    all_goals simpa [low, high, quotientState, constructQuotient, StatusFlags.from_result,
      Effects.All] using next _

theorem capacity_guard (e : Executable) (base : Int64) (hc : CodeAt e base)
    (list : Bool) (s : MachineData) (fits : s.regs.r13.toNat ≤ s.regs.r9.toNat)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P ({s with status := flags}, base + if list then 452 else 696)) :
    Eventually (step e) P (s, base + if list then 443 else 687) := by
  have notBelow : ¬ s.regs.r9.toNat < s.regs.r13.toNat := Nat.not_lt.mpr fits
  cases list
  · emit_step 140 using hc
    emit_step 141 using hc
    simpa [StatusFlags.from_result, Udivti3.cf_sub, notBelow, Effects.All] using next _
  · emit_step 75 using hc
    emit_step 76 using hc
    simpa [StatusFlags.from_result, Udivti3.cf_sub, notBelow, Effects.All] using next _

end SszX86.Emit.Bits
