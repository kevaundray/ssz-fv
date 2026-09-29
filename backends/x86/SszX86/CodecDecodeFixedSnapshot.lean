import SszX86.CodecDecodeFixedExec

set_option autoImplicit false

namespace SszX86.CodecDecodeFixed
open SszNative UintCodec
open CodecDeserialize (ValueWords)

/-- Compiler spill order between the complete child loads and destination stores. -/
def snapshotMem (m : DataMem) (sp : BitVec 64) (words : ValueWords) : DataMem :=
  let m := Mem.storeInt m (sp + 120) 8 words.w5.toInt
  let m := Mem.storeInt m (sp + 112) 8 words.w4.toInt
  let m := Mem.storeInt m (sp + 104) 8 words.w3.toInt
  let m := Mem.storeInt m (sp + 96) 8 words.w2.toInt
  Mem.storeInt m (sp + 88) 8 words.w1.toInt

def snapshotState (s : MachineData) (words : ValueWords) : MachineData :=
  {s with regs := {s.regs with
    rax := UInt64.ofBitVec words.w0, rcx := UInt64.ofBitVec words.w1,
    rdx := UInt64.ofBitVec words.w2, rsi := UInt64.ofBitVec words.w3,
    rdi := UInt64.ofBitVec words.w4, r8 := UInt64.ofBitVec words.w5},
    dmem := snapshotMem s.dmem s.regs.rsp.toBitVec words}

macro "codec_fixed_snapshot_store " row:num " offset " off:num
    " using " hc:term " mapped " hm:term : tactic => `(tactic|
  (codec_fixed_core_step SszX86.CodecDecodeFixed.programChunk1 row $row using $hc
   simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
   apply Delimited.store_cps
   · apply Large.mapped_load (capacity := 264) (offset := $off) («width» := 8)
     · repeat' first | exact $hm | apply Large.mapped_store
     · decide
   simp only [Effects.All]))

/-- All six source words are loaded before any destination word is initialized.
The words include arbitrary padding; the shared NodeAt relation uses only their
active fields after the verbatim copy. -/
theorem snapshot_runs (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (words : ValueWords)
    (input : words.At s.dmem (s.regs.rsp.toBitVec + 144))
    (payload : s.regs.r12.toBitVec = s.regs.rsp.toBitVec + 152)
    (mapped : Large.Mapped s.dmem s.regs.rsp.toBitVec 264) :
    Eventually (step e) (fun t => t = (snapshotState s words, base + 511))
      (s, base + 454) := by
  have l0 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 144) 8 = some (words.w0.toNat : Int) := by
    simpa only [BitVec.add_zero] using input.w0
  have l1 : Mem.loadInt s.dmem s.regs.r12.toBitVec 8 = some (words.w1.toNat : Int) := by
    rw [payload]
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using input.w1
  have l2 : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 8) 8 = some (words.w2.toNat : Int) := by
    rw [payload]
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using input.w2
  have l3 : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 16) 8 = some (words.w3.toNat : Int) := by
    rw [payload]
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using input.w3
  have l4 : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 24) 8 = some (words.w4.toNat : Int) := by
    rw [payload]
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using input.w4
  have l5 : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 32) 8 = some (words.w5.toNat : Int) := by
    rw [payload]
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using input.w5
  codec_fixed_core_step programChunk1 row 40 using code
  codec_fixed_core_load l0
  codec_fixed_core_step programChunk1 row 41 using code
  codec_fixed_core_load l1
  codec_fixed_core_step programChunk1 row 42 using code
  codec_fixed_core_load l2
  codec_fixed_core_step programChunk1 row 43 using code
  codec_fixed_core_load l3
  codec_fixed_core_step programChunk1 row 44 using code
  codec_fixed_core_load l4
  codec_fixed_core_step programChunk1 row 45 using code
  codec_fixed_core_load l5
  codec_fixed_snapshot_store 46 offset 120 using code mapped mapped
  codec_fixed_snapshot_store 47 offset 112 using code mapped mapped
  codec_fixed_snapshot_store 48 offset 104 using code mapped mapped
  codec_fixed_snapshot_store 49 offset 96 using code mapped mapped
  codec_fixed_snapshot_store 50 offset 88 using code mapped mapped
  apply Eventually.done
  rfl

/-- The private spill array contains precisely the five trailing loaded words. -/
theorem snapshot_loads (m : DataMem) (sp : BitVec 64) (words : ValueWords) :
    Mem.loadInt (snapshotMem m sp words) (sp + 88) 8 = some (words.w1.toNat : Int) ∧
    Mem.loadInt (snapshotMem m sp words) (sp + 96) 8 = some (words.w2.toNat : Int) ∧
    Mem.loadInt (snapshotMem m sp words) (sp + 104) 8 = some (words.w3.toNat : Int) ∧
    Mem.loadInt (snapshotMem m sp words) (sp + 112) 8 = some (words.w4.toNat : Int) ∧
    Mem.loadInt (snapshotMem m sp words) (sp + 120) 8 = some (words.w5.toNat : Int) := by
  have keep (memory : DataMem) (a b : Nat) (value : Int)
      (ha : a + 8 ≤ 264) (hb : b + 8 ≤ 264) (apart : a + 8 ≤ b ∨ b + 8 ≤ a) :
      Mem.loadInt (Mem.storeInt memory (sp + BitVec.ofNat 64 b) 8 value)
        (sp + BitVec.ofNat 64 a) 8 = Mem.loadInt memory (sp + BitVec.ofNat 64 a) 8 := by
    apply BoolCodec.load_store_disjoint
    intro i hi j hj
    bv_omega
  simp (disch := first | omega | decide) only
    [snapshotMem, keep, Serialize.Publish.load_store_word]

end SszX86.CodecDecodeFixed
