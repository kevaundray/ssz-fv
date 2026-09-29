import SszX86.CodecMeasureChildDecode
import SszX86.Udivti3Math

namespace SszX86.CodecMeasureChild
open BoolCodec UintCodec
open Kraken.X64.Parser

/-- State immediately before the real recursive CALL at local PC101. The
selected child is addressed using the actual Value stride48 instructions. -/
def measureCallState (s : MachineData) (values keepPointer : BitVec 64)
    (keep : Bool) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    rax := UInt64.ofBitVec keepPointer,
    rdx := UInt64.ofBitVec (s.regs.rdx.toBitVec * 48 + values),
    r8 := UInt64.ofNat (if keep then 1 else 0),
    rdi := s.regs.rsp, rsi := s.regs.rbp, rcx := s.regs.r14}, status := flags}

/-- The value-bound panic is excluded by the physical paired-prefix index,
then the capture's keep byte becomes the recursive retain argument. -/
theorem value_prepare (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (count : Nat) (values keepPointer : BitVec 64) (keep : Bool)
    (P : MachineState → Prop)
    (countBound : count < 2 ^ 64) (index : s.regs.rdx.toNat < count)
    (countLoad : Mem.loadInt s.dmem (s.regs.r13.toBitVec + 16) 8 = some (count : Int))
    (valuesLoad : Mem.loadInt s.dmem (s.regs.r13.toBitVec + 8) 8 = some (values.toNat : Int))
    (keepPointerLoad : Mem.loadInt s.dmem (s.regs.r13.toBitVec + 24) 8 =
      some (keepPointer.toNat : Int))
    (keepLoad : Mem.loadInt s.dmem keepPointer 1 = some (if keep then 1 else 0))
    (next : ∀ flags, Eventually (step e) P
      (measureCallState s values keepPointer keep flags, base + 101)) :
    Eventually (step e) P (s, base + 59) := by
  have indexWord : s.regs.rdx.toBitVec.toNat < (BitVec.ofNat 64 count).toNat := by
    simpa only [UInt64.toNat_toBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound] using index
  have scale : (s.regs.rdx.toBitVec + s.regs.rdx.toBitVec * 2) <<< 4 =
      s.regs.rdx.toBitVec * 48 := by bv_omega
  codec_measure_child_step 19 using code
  simp only [MachineData.load, Effects.All, countLoad,
    show Width.W64.bytes = 8 by rfl, show Width.W64.bits = 64 by rfl, BitVec.ofInt_ofNat]
  codec_measure_child_step 20 using code
  codec_measure_child_step 21 using code
  simp only [StatusFlags.from_result, Udivti3.cf_sub, indexWord, decide_true,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  codec_measure_child_step 22 using code
  codec_measure_child_step 23 using code
  simp (config := {instances := true}) [ShiftCountExpr.interpMasked, ShiftCountExpr.interp,
    ConstExpr.interp, BitVec.take, Effects.All]
  constructor <;> constructor
  all_goals
    codec_measure_child_step 24 using code
    simp only [MachineData.load, Effects.All, valuesLoad,
      show Width.W64.bytes = 8 by rfl, show Width.W64.bits = 64 by rfl,
      Delimited.word_cast]
    codec_measure_child_step 25 using code
    simp only [MachineData.load, Effects.All, keepPointerLoad,
      show Width.W64.bytes = 8 by rfl, show Width.W64.bits = 64 by rfl,
      Delimited.word_cast]
    codec_measure_child_step 26 using code
    simp only [MachineData.load, Effects.All, keepLoad,
      show Width.W8.bytes = 1 by rfl, show Width.W8.bits = 8 by rfl]
    codec_measure_child_step 27 using code
    codec_measure_child_step 28 using code
    codec_measure_child_step 29 using code
    cases keep <;> simpa [measureCallState, scale, UInt64.ofNat, StatusFlags.from_result,
      Effects.All] using next _

def callState (s : MachineData) (ra : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 8)}
    dmem := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8) 8 ra.toInt}

/-- The real recursive CALL writes return PC106 and transfers to the original
measure entry at its linked offset. It is not a recursive execution oracle. -/
theorem measure_call (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    («mapped» : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old)
    (next : Eventually (step e) P
      (callState s (base + 106).toBitVec, base + Int64.ofInt measureOffset)) :
    Eventually (step e) P (s, base + 101) := by
  codec_measure_child_step 30 using code
  apply Delimited.store_cps
  · simpa using «mapped»
  · simpa [callState, Effects.All, measureOffset, Int64.add_assoc] using next

end SszX86.CodecMeasureChild
