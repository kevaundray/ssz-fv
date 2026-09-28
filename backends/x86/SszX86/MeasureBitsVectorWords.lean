import SszX86.MeasureBitsVectorCompare
import SszX86.MeasureBitsVectorMath

namespace SszX86.Measure.Bits
open SszNative UintCodec

def vectorLowPair (s : MachineData) (lo hi : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r9 := UInt64.ofBitVec lo
      rdi := UInt64.ofBitVec lo
      r8 := UInt64.ofBitVec hi}
    status := flags}

/-- Physical length drives the real first/second loads even when significant
length is zero. No canonicality of the borrowed list is used. -/
theorem vector_low_words_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64))
    (nonempty : words ≠ []) (bound : words.length < 2^64)
    (payload : s.regs.rdi.toBitVec = BitVec.ofNat 64 words.length)
    (stored : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.r8.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (vectorLowPair s (words[0]?.getD 0#64) (words[1]?.getD 0#64) flags, base + 2785)) :
    Eventually (step e) P (s, base + 1863) := by
  have positive : 0 < words.length := by cases words <;> simp_all
  have first : Mem.loadInt s.dmem s.regs.r8.toBitVec 8 =
      some ((words[0]?.getD 0#64).toNat : Int) := by
    simpa [List.getElem?_eq_getElem positive] using stored ⟨0, positive⟩
  have count : s.regs.rdi.toNat = words.length := by
    have equal := congrArg BitVec.toNat payload
    simpa only [UInt64.toNat_toBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using equal
  apply vector_low_word_cps e base hc s _ P first
  intro flags
  by_cases one : words.length < 2
  · simp only [count, one, ↓reduceIte]
    apply vector_one_high_cps e base hc
    intro flags'
    apply vector_pair_join_cps e base hc
    have second : words[1]?.getD 0#64 = 0#64 := by
      rw [List.getElem?_eq_none (by omega)]
      rfl
    simpa only [vectorLowPair, second, UInt64.ofBitVec_ofNat] using next flags'
  · simp only [count, one, ↓reduceIte]
    apply vector_high_word_cps e base hc (high := words[1]?.getD 0#64)
    · simpa [List.getElem?_eq_getElem (show 1 < words.length by omega)] using stored ⟨1, by omega⟩
    apply vector_pair_join_cps e base hc
    simpa only [vectorLowPair] using next flags

/-- Scratch registers may change during normalization/equality, but all source,
count, arena, result and activation registers retain their original values. -/
structure VectorReadFrame (s t : MachineData) : Prop where
  memory : t.dmem = s.dmem
  vectors : t.zmms = s.zmms
  output : t.regs.rbx = s.regs.rbx
  stack : t.regs.rsp = s.regs.rsp
  descriptor : t.regs.rsi = s.regs.rsi
  input : t.regs.r14 = s.regs.r14
  arena : t.regs.rcx = s.regs.rcx
  low : t.regs.rax = s.regs.rax
  high : t.regs.rdx = s.regs.rdx

end SszX86.Measure.Bits
