import SszX86.BitVectorStackPair
import SszX86.BitVectorRound

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

theorem stack_pair_observed (m : DataMem) (sp : BitVec 64) (off : Nat) (first second : BitVec 64)
    (high : sp.toNat + 224 ≤ 2^64) (inside : off + 16 ≤ 224) :
    widthLoad (stackPairMem m sp off first second) (sp.toNat + off) 8 = some first.toNat ∧
    widthLoad (stackPairMem m sp off first second) (sp.toNat + off + 8) 8 = some second.toNat := by
  have input := stack_pair_reads m sp off first second high inside
  constructor
  · unfold widthLoad
    rw [width_address, input.1]
    rfl
  · unfold widthLoad
    rw [Nat.add_assoc, width_address, input.2]
    rfl

theorem round_stage_world {s u : MachineData} {saved : Saved} {length : NatOperand}
    {data : Ssz.Bytes} {address capacity initialUsed currentUsed : BitVec 64}
    {writes : List (Nat × Nat)}
    (world : World s saved length data address capacity initialUsed currentUsed writes u.dmem)
    (anchors : Anchors s u length) (pointer payload : BitVec 64) (flags : StatusFlags) :
    World s saved length data address capacity initialUsed currentUsed writes
      (roundBranchState u pointer payload flags).dmem := by
  simpa only [roundBranchState, expectedPairMem, stackPairMem, anchors.stack] using
    world.stack_pair 208 pointer payload (by decide)

theorem round_stage_anchors {s u : MachineData} {length : NatOperand}
    (anchors : Anchors s u length) (high : s.regs.rsp.toNat + 368 ≤ 2^64)
    (pointer payload : BitVec 64) (flags : StatusFlags) :
    Anchors s (roundBranchState u pointer payload flags) length := by
  have highBV : s.regs.rsp.toBitVec.toNat + 224 ≤ 2^64 := by
    change s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 at high
    omega
  apply anchors.fixed (v := roundBranchState u pointer payload flags) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simpa only [roundBranchState, expectedPairMem, stackPairMem, anchors.stack] using
      (stack_pair_read u.dmem s.regs.rsp.toBitVec 208 8 8 pointer payload highBV
        (by decide) (by decide) (Or.inl (by decide))).trans anchors.outputCache
  · simpa only [roundBranchState, expectedPairMem, stackPairMem, anchors.stack] using
      (stack_pair_read u.dmem s.regs.rsp.toBitVec 208 104 8 pointer payload highBV
        (by decide) (by decide) (Or.inl (by decide))).trans anchors.sourceCache

theorem round_stage_frame {s u : MachineData} {length : NatOperand}
    (anchors : Anchors s u length) (low : 72 ≤ s.regs.rsp.toNat)
    (high : s.regs.rsp.toNat + 368 ≤ 2^64) (pointer payload : BitVec 64) (flags : StatusFlags) :
    RegionsFrame u.dmem (roundBranchState u pointer payload flags).dmem [(workStart s, workSize)] := by
  simpa only [roundBranchState, expectedPairMem, stackPairMem, anchors.stack] using
    stack_pair_regions s u.dmem 208 pointer payload low high (by decide)

theorem round_stage_operand {s u : MachineData} {length expected : NatOperand}
    {address capacity used : BitVec 64} (anchors : Anchors s u length)
    (low : 72 ≤ s.regs.rsp.toNat) (high : s.regs.rsp.toNat + 368 ≤ 2^64)
    (stored : expected.At (widthLoad u.dmem)) (hp : OperandProtected s address capacity used expected)
    (flags : StatusFlags) :
    NatArithmetic.operandAt
      (widthLoad (roundBranchState u expected.pointer expected.payload flags).dmem)
      (s.regs.rsp.toNat + 208) expected := by
  have highBV : s.regs.rsp.toBitVec.toNat + 224 ≤ 2^64 := by
    change s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 at high
    omega
  have pair := stack_pair_observed u.dmem s.regs.rsp.toBitVec 208 expected.pointer expected.payload
    highBV (by decide)
  have frame := round_stage_frame anchors low high expected.pointer expected.payload flags
  refine ⟨?_, ?_, work_frame_operand frame expected stored hp⟩
  · simpa only [roundBranchState, expectedPairMem, stackPairMem, anchors.stack,
      UInt64.toNat_toBitVec] using pair.1
  · simpa only [roundBranchState, expectedPairMem, stackPairMem, anchors.stack,
      UInt64.toNat_toBitVec] using pair.2

theorem round_branch_owned_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s u : MachineData) (saved : Saved) (length quotient : NatOperand) (data : Ssz.Bytes)
    (address capacity initialUsed currentUsed : BitVec 64) (writes : List (Nat × Nat))
    (world : World s saved length data address capacity initialUsed currentUsed writes u.dmem)
    (anchors : Anchors s u length)
    (stored : quotient.At (widthLoad u.dmem)) (hp : OperandProtected s address capacity currentUsed quotient)
    (hpointer : Mem.loadInt u.dmem (s.regs.rsp.toBitVec + 120#64) 8 = some (quotient.pointer.toNat : Int))
    (hpayload : Mem.loadInt u.dmem (s.regs.rsp.toBitVec + 128#64) 8 = some (quotient.payload.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags,
      World s saved length data address capacity initialUsed currentUsed writes
        (roundBranchState u quotient.pointer quotient.payload flags).dmem →
      Anchors s (roundBranchState u quotient.pointer quotient.payload flags) length →
      NatArithmetic.operandAt (widthLoad (roundBranchState u quotient.pointer quotient.payload flags).dmem)
        (s.regs.rsp.toNat + 208) quotient →
      RegionsFrame u.dmem (roundBranchState u quotient.pointer quotient.payload flags).dmem
        [(workStart s, workSize)] →
      Eventually (step e) P (roundBranchState u quotient.pointer quotient.payload flags,
        if u.regs.r13.toBitVec = 0#64 then base + 4618 else base + 1727)) :
    Eventually (step e) P (u, base + 1689) := by
  have low : 72 ≤ s.regs.rsp.toNat := world.physical.stack_low
  have high : s.regs.rsp.toNat + 368 ≤ 2^64 := world.physical.stack_bound
  apply round_branch_cps e base hc u quotient.pointer quotient.payload
  · simpa only [anchors.stack] using world.physical.body_mapped
  · simpa only [anchors.stack] using hpointer
  · simpa only [anchors.stack] using hpayload
  · intro flags
    exact next flags (round_stage_world world anchors quotient.pointer quotient.payload flags)
      (round_stage_anchors anchors high quotient.pointer quotient.payload flags)
      (round_stage_operand anchors low high stored hp flags)
      (round_stage_frame anchors low high quotient.pointer quotient.payload flags)

end SszX86.BitVector
