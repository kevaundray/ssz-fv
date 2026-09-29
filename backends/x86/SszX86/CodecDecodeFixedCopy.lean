import SszX86.CodecDecodeFixedSnapshot

set_option autoImplicit false

namespace SszX86.CodecDecodeFixed
open SszNative UintCodec
open CodecDeserialize (ValueWords)

/-- Compiler-private spill fields used by the literal fill-loop copy. -/
def SpillAt (m : DataMem) (sp : BitVec 64) (words : ValueWords) : Prop :=
  Mem.loadInt m (sp + 88) 8 = some (words.w1.toNat : Int) ∧
  Mem.loadInt m (sp + 96) 8 = some (words.w2.toNat : Int) ∧
  Mem.loadInt m (sp + 104) 8 = some (words.w3.toNat : Int) ∧
  Mem.loadInt m (sp + 112) 8 = some (words.w4.toNat : Int) ∧
  Mem.loadInt m (sp + 120) 8 = some (words.w5.toNat : Int)

def copiedState (s : MachineData) (destination : BitVec 64) (words : ValueWords) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofBitVec words.w5, rcx := UInt64.ofBitVec words.w2},
    dmem := CodecDeserialize.copyWords s.dmem destination words}

macro "codec_fixed_copy_store " row:num " offset " off:num
    " using " hc:term " mapped " hm:term " pointer " hp:term : tactic => `(tactic|
  (codec_fixed_core_step SszX86.CodecDecodeFixed.programChunk1 row $row using $hc
   simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, ($hp), BitVec.add_assoc,
     BitVec.reduceAdd, BitVec.add_zero]
   apply Delimited.store_cps
   · have available := Large.mapped_load _ _ 48 $off 8
       (by repeat' first | exact $hm | apply Large.mapped_store) (by decide)
     simpa only [BitVec.ofNat_zero, BitVec.add_zero] using available
   simp only [Effects.All]))

/-- The exact post-success copy from the helper's saved words into one allocated
Value slot. No allocation or recursive call is assumed in this instruction cut. -/
theorem copy_runs (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (destination : BitVec 64) (words : ValueWords)
    (pointer : s.regs.r15.toBitVec = destination + 8)
    (first : s.regs.rax.toBitVec = words.w0)
    (spill : SpillAt s.dmem s.regs.rsp.toBitVec words)
    (mapped : Large.Mapped s.dmem destination 48)
    (separate : ∀ i < 40, ∀ j < 48,
      s.regs.rsp.toBitVec + 88 + BitVec.ofNat 64 i ≠ destination + BitVec.ofNat 64 j) :
    Eventually (step e) (fun t => t = (copiedState s destination words, base + 559))
      (s, base + 511) := by
  have keep (memory : DataMem) (a b : Nat) (value : Int)
      (low : 88 ≤ a) (high : a + 8 ≤ 128) (width : b + 8 ≤ 48) :
      Mem.loadInt (Mem.storeInt memory (destination + BitVec.ofNat 64 b) 8 value)
        (s.regs.rsp.toBitVec + BitVec.ofNat 64 a) 8 =
      Mem.loadInt memory (s.regs.rsp.toBitVec + BitVec.ofNat 64 a) 8 := by
    apply BoolCodec.load_store_disjoint
    intro i hi j hj
    have address : s.regs.rsp.toBitVec + BitVec.ofNat 64 a + BitVec.ofNat 64 i =
        s.regs.rsp.toBitVec + 88 + BitVec.ofNat 64 (a - 88 + i) := by
      simp only [BitVec.ofNat_add, BitVec.add_assoc]
      bv_omega
    rw [address, memmove_addr_add]
    exact separate (a - 88 + i) (by omega) (b + j) (by omega)
  have keep0 (memory : DataMem) (a : Nat) (value : Int)
      (low : 88 ≤ a) (high : a + 8 ≤ 128) :
      Mem.loadInt (Mem.storeInt memory destination 8 value)
        (s.regs.rsp.toBitVec + BitVec.ofNat 64 a) 8 =
      Mem.loadInt memory (s.regs.rsp.toBitVec + BitVec.ofNat 64 a) 8 := by
    simpa only [BitVec.ofNat_zero, BitVec.add_zero] using keep memory a 0 value low high (by decide)
  codec_fixed_core_step programChunk1 row 51 using code
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, pointer, first,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]
  apply Delimited.store_cps
  · have available := Large.mapped_load s.dmem destination 48 0 8 mapped (by decide)
    simpa only [BitVec.ofNat_zero, BitVec.add_zero] using available
  simp only [Effects.All]
  codec_fixed_core_step programChunk1 row 52 using code
  simp (disch := first | omega | decide) only [keep0, keep]
  codec_fixed_core_load spill.1
  codec_fixed_core_step programChunk1 row 53 using code
  simp (disch := first | omega | decide) only [keep0, keep]
  codec_fixed_core_load spill.2.1
  codec_fixed_copy_store 54 offset 8 using code mapped mapped pointer pointer
  codec_fixed_copy_store 55 offset 16 using code mapped mapped pointer pointer
  codec_fixed_core_step programChunk1 row 56 using code
  simp (disch := first | omega | decide) only [keep0, keep]
  codec_fixed_core_load spill.2.2.1
  codec_fixed_copy_store 57 offset 24 using code mapped mapped pointer pointer
  codec_fixed_core_step programChunk1 row 58 using code
  simp (disch := first | omega | decide) only [keep0, keep]
  codec_fixed_core_load spill.2.2.2.1
  codec_fixed_copy_store 59 offset 32 using code mapped mapped pointer pointer
  codec_fixed_core_step programChunk1 row 60 using code
  simp (disch := first | omega | decide) only [keep0, keep]
  codec_fixed_core_load spill.2.2.2.2
  codec_fixed_copy_store 61 offset 40 using code mapped mapped pointer pointer
  apply Eventually.done
  rfl

end SszX86.CodecDecodeFixed
