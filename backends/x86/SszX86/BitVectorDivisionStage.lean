import SszX86.BitVectorStackPair
import SszX86.BitVectorDivisionResult

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

theorem division_stage_world {s u : MachineData} {saved : Saved} {length : NatOperand}
    {data : Ssz.Bytes} {address capacity initialUsed currentUsed : BitVec 64}
    {writes : List (Nat × Nat)}
    (world : World s saved length data address capacity initialUsed currentUsed writes u.dmem)
    (anchors : Anchors s u length) (pointer payload remainder : BitVec 64)
    (statusWord : BitVec 32) (flags : StatusFlags) :
    World s saved length data address capacity initialUsed currentUsed writes
      (divisionResultState u pointer payload remainder statusWord flags).dmem := by
  simpa only [divisionResultState, divisionResultMem, stackPairMem, anchors.stack] using
    world.stack_pair 120 pointer payload (by decide)

theorem division_stage_anchors {s u : MachineData} {length : NatOperand}
    (anchors : Anchors s u length) (high : s.regs.rsp.toNat + 368 ≤ 2^64)
    (pointer payload remainder : BitVec 64) (statusWord : BitVec 32) (flags : StatusFlags) :
    Anchors s (divisionResultState u pointer payload remainder statusWord flags) length := by
  have highBV : s.regs.rsp.toBitVec.toNat + 224 ≤ 2^64 := by
    change s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 at high
    omega
  apply anchors.fixed (v := divisionResultState u pointer payload remainder statusWord flags)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simpa only [divisionResultState, divisionResultMem, stackPairMem, anchors.stack] using
      (stack_pair_read u.dmem s.regs.rsp.toBitVec 120 8 8 pointer payload highBV
        (by decide) (by decide) (Or.inl (by decide))).trans anchors.outputCache
  · simpa only [divisionResultState, divisionResultMem, stackPairMem, anchors.stack] using
      (stack_pair_read u.dmem s.regs.rsp.toBitVec 120 104 8 pointer payload highBV
        (by decide) (by decide) (Or.inl (by decide))).trans anchors.sourceCache

theorem division_stage_frame {s u : MachineData} {length : NatOperand}
    (anchors : Anchors s u length) (low : 72 ≤ s.regs.rsp.toNat)
    (high : s.regs.rsp.toNat + 368 ≤ 2^64) (pointer payload remainder : BitVec 64)
    (statusWord : BitVec 32) (flags : StatusFlags) :
    RegionsFrame u.dmem (divisionResultState u pointer payload remainder statusWord flags).dmem
      [(workStart s, workSize)] := by
  simpa only [divisionResultState, divisionResultMem, stackPairMem, anchors.stack] using
    stack_pair_regions s u.dmem 120 pointer payload low high (by decide)

theorem division_stage_private {s u : MachineData} {length : NatOperand}
    (anchors : Anchors s u length) (high : s.regs.rsp.toNat + 368 ≤ 2^64)
    (pointer payload remainder : BitVec 64) (statusWord : BitVec 32) (flags : StatusFlags)
    (off count : Nat) (inside : off + count ≤ 120) :
    widthLoad (divisionResultState u pointer payload remainder statusWord flags).dmem
        (s.regs.rsp.toNat + off) count = widthLoad u.dmem (s.regs.rsp.toNat + off) count := by
  have highBV : s.regs.rsp.toBitVec.toNat + 224 ≤ 2^64 := by
    change s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 at high
    omega
  change Option.map Int.toNat (Mem.loadInt _ (BitVec.ofNat 64 (s.regs.rsp.toBitVec.toNat + off)) count) =
    Option.map Int.toNat (Mem.loadInt _ (BitVec.ofNat 64 (s.regs.rsp.toBitVec.toNat + off)) count)
  rw [width_address]
  congr 1
  simpa only [divisionResultState, divisionResultMem, stackPairMem, anchors.stack] using
    stack_pair_read u.dmem s.regs.rsp.toBitVec 120 off count pointer payload highBV
      (by decide) (by omega) (Or.inl inside)

theorem division_stage_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s u : MachineData) (saved : Saved) (length : NatOperand) (data : Ssz.Bytes)
    (address capacity initialUsed currentUsed : BitVec 64) (writes : List (Nat × Nat))
    (world : World s saved length data address capacity initialUsed currentUsed writes u.dmem)
    (anchors : Anchors s u length) (pointer payload remainder : BitVec 64) (statusWord : BitVec 32)
    (hstatus : Mem.loadInt u.dmem (s.regs.rsp.toBitVec + 80#64) 4 = some (statusWord.toNat : Int))
    (hpointer : Mem.loadInt u.dmem (s.regs.rsp.toBitVec + 16#64) 8 = some (pointer.toNat : Int))
    (hpayload : Mem.loadInt u.dmem (s.regs.rsp.toBitVec + 24#64) 8 = some (payload.toNat : Int))
    (hremainder : Mem.loadInt u.dmem (s.regs.rsp.toBitVec + 32#64) 8 = some (remainder.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags,
      World s saved length data address capacity initialUsed currentUsed writes
        (divisionResultState u pointer payload remainder statusWord flags).dmem →
      Anchors s (divisionResultState u pointer payload remainder statusWord flags) length →
      RegionsFrame u.dmem (divisionResultState u pointer payload remainder statusWord flags).dmem
        [(workStart s, workSize)] →
      Eventually (step e) P (divisionResultState u pointer payload remainder statusWord flags,
        if statusWord = 0#32 then base + 1689 else base + 197)) :
    Eventually (step e) P (u, base + 157) := by
  have low : 72 ≤ s.regs.rsp.toNat := world.physical.stack_low
  have high : s.regs.rsp.toNat + 368 ≤ 2^64 := world.physical.stack_bound
  have highBV : s.regs.rsp.toBitVec.toNat + 224 ≤ 2^64 := by
    change s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 at high
    omega
  apply division_result_cps e base hc u pointer payload remainder statusWord
  · simpa only [anchors.stack] using world.physical.body_mapped
  · simpa only [anchors.stack] using hstatus
  · simpa only [anchors.stack] using hpointer
  · simpa only [anchors.stack] using hpayload
  · simpa only [divisionResultMem, stackPairMem, anchors.stack] using
      (stack_pair_read u.dmem s.regs.rsp.toBitVec 120 32 8 pointer payload highBV
        (by decide) (by decide) (Or.inl (by decide))).trans hremainder
  · intro flags
    exact next flags (division_stage_world world anchors pointer payload remainder statusWord flags)
      (division_stage_anchors anchors high pointer payload remainder statusWord flags)
      (division_stage_frame anchors low high pointer payload remainder statusWord flags)

end SszX86.BitVector
