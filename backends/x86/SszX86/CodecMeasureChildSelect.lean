import SszX86.CodecMeasureChildDecode
import SszX86.Udivti3Math

namespace SszX86.CodecMeasureChild
open BoolCodec UintCodec

macro "codec_measure_child_load " loaded:term : tactic => `(tactic|
  simp (config := {instances := true})
    [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, ($loaded), Delimited.word_cast])

def repeatedState (s : MachineData) (parts child : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with r15 := UInt64.ofBitVec parts,
    rax := 0, rbp := UInt64.ofBitVec child}, status := flags}

/-- The zero niche reads the descriptor pointer directly from Parts+8; there is
no field-bound guard in the repeated branch of the real closure. -/
theorem repeated_select (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (parts child : BitVec 64) (P : MachineState → Prop)
    (partsLoad : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (parts.toNat : Int))
    (tagLoad : Mem.loadInt s.dmem parts 8 = some 0)
    (childLoad : Mem.loadInt s.dmem (parts + 8) 8 = some (child.toNat : Int))
    (next : ∀ flags, Eventually (step e) P (repeatedState s parts child flags, base + 59)) :
    Eventually (step e) P (s, base + 26) := by
  have target := code.targets ("codec_measure_child_u59", 59) (by decide)
  codec_measure_child_step 10 using code
  codec_measure_child_load partsLoad
  codec_measure_child_step 11 using code
  codec_measure_child_load tagLoad
  codec_measure_child_step 12 using code
  codec_measure_child_load childLoad
  codec_measure_child_step 13 using code
  constructor <;> codec_measure_child_step 14 using code
  all_goals simpa [repeatedState, StatusFlags.from_result, target, Effects.All] using next _

def fieldsState (s : MachineData) (parts fields child : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with r15 := UInt64.ofBitVec parts,
    rax := UInt64.ofBitVec fields, rbp := UInt64.ofBitVec child,
    rcx := UInt64.ofBitVec (s.regs.rdx.toBitVec + s.regs.rdx.toBitVec * 2)}, status := flags}

/-- The field bound is checked before the value bound. A paired-prefix index
satisfies both without assuming equal arities or a well-formed descriptor. -/
theorem fields_select (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (parts fields child : BitVec 64) (count : Nat)
    (P : MachineState → Prop)
    (partsLoad : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (parts.toNat : Int))
    (fieldsLoad : Mem.loadInt s.dmem parts 8 = some (fields.toNat : Int))
    (countLoad : Mem.loadInt s.dmem (parts + 8) 8 = some (count : Int))
    (nonnull : 0 < fields.toNat) (countBound : count < 2 ^ 64)
    (index : s.regs.rdx.toNat < count)
    (childLoad : Mem.loadInt s.dmem
      (fields + (s.regs.rdx.toBitVec + s.regs.rdx.toBitVec * 2) * 8 + 16) 8 =
        some (child.toNat : Int))
    (next : ∀ flags, Eventually (step e) P (fieldsState s parts fields child flags, base + 59)) :
    Eventually (step e) P (s, base + 26) := by
  have nonzero : fields ≠ 0 := by
    intro equal
    have zero := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_zero] at zero
    omega
  have indexWord : s.regs.rdx.toBitVec.toNat < (BitVec.ofNat 64 count).toNat := by
    simpa only [UInt64.toNat_toBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound] using index
  codec_measure_child_step 10 using code
  codec_measure_child_load partsLoad
  codec_measure_child_step 11 using code
  codec_measure_child_load fieldsLoad
  codec_measure_child_step 12 using code
  codec_measure_child_load countLoad
  codec_measure_child_step 13 using code
  constructor <;> codec_measure_child_step 14 using code
  all_goals
    simp only [StatusFlags.from_result, nonzero, Bool.false_eq_true, ↓reduceIte]
    codec_measure_child_step 15 using code
    codec_measure_child_step 16 using code
    simp only [StatusFlags.from_result, Udivti3.cf_sub, indexWord, decide_true,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    codec_measure_child_step 17 using code
    codec_measure_child_step 18 using code
    codec_measure_child_load childLoad
    simpa [fieldsState, Effects.All] using next _

end SszX86.CodecMeasureChild
