import SszX86.CodecEmitPartsEntry

namespace SszX86.CodecEmitParts

/-- The optional-plan discriminant is the literal pointer niche. -/
theorem plan_none_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop) (zero : s.status.zf = true)
    (next : Eventually (step e) P (s, base + 558)) :
    Eventually (step e) P (s, base + 33) := by
  have target := code.targets ("codec_emit_parts_u558", 558) (by decide)
  codec_parts_step 11 using code
  simpa only [zero, target, ↓reduceIte, Effects.All] using next

theorem plan_some_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop) (nonzero : s.status.zf = false)
    (next : Eventually (step e) P (s, base + 39)) :
    Eventually (step e) P (s, base + 33) := by
  codec_parts_step 11 using code
  simpa only [nonzero, Bool.false_eq_true, ↓reduceIte, Effects.All] using next

/-- A present root plan with no children deliberately selects the same native
sequential loop as None. The leading word remains completely unread. -/
theorem empty_children_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (empty : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 8) 8 = some 0)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with r14 := 0}, status := flags}, base + 558)) :
    Eventually (step e) P (s, base + 39) := by
  have target := code.targets ("codec_emit_parts_u558", 558) (by decide)
  codec_parts_step 12 using code
  simp only [MachineData.load, empty, Effects.All, BitVec.ofInt_zero]
  codec_parts_step 13 using code
  constructor <;> codec_parts_step 14 using code
  all_goals simpa [target, StatusFlags.from_result, Effects.All] using next _

def tableEntryState (s : MachineData) (leading : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with r14 := s.regs.rcx, rbp := UInt64.ofBitVec leading}, status := flags}

/-- Generated child count equals actual value count, so the real CMOV-min cannot
truncate traversal. The leading cursor is read only on this nonempty branch. -/
theorem retained_children_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (leading : BitVec 64) (P : MachineState → Prop)
    (count : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 8) 8 = some (s.regs.rcx.toNat : Int))
    (start : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 32) 8 = some (leading.toNat : Int))
    (nonempty : s.regs.rcx.toBitVec ≠ 0#64)
    (next : ∀ flags, Eventually (step e) P (tableEntryState s leading flags, base + 72)) :
    Eventually (step e) P (s, base + 39) := by
  have cast : BitVec.ofInt 64 (s.regs.rcx.toNat : Int) = s.regs.rcx.toBitVec := by bv_omega
  codec_parts_step 12 using code
  simp only [MachineData.load, count, Effects.All, cast]
  codec_parts_step 13 using code
  constructor <;> codec_parts_step 14 using code
  all_goals simp [nonempty, StatusFlags.from_result, Effects.All]
  all_goals codec_parts_step 15 using code
  all_goals codec_parts_load start
  all_goals codec_parts_step 16 using code
  all_goals codec_parts_step 17 using code
  all_goals simp [StatusFlags.from_result, Effects.All]
  all_goals codec_parts_step 18 using code
  all_goals constructor
  all_goals codec_parts_step 19 using code
  all_goals simpa [tableEntryState, nonempty, StatusFlags.from_result, Effects.All] using next _

end SszX86.CodecEmitParts
