import SszX86.BitVectorReached

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

def stackPairMem (m : DataMem) (sp : BitVec 64) (off : Nat) (first second : BitVec 64) : DataMem :=
  Mem.storeInt (Mem.storeInt m (sp + BitVec.ofNat 64 off) 8 first.toInt)
    (sp + BitVec.ofNat 64 (off + 8)) 8 second.toInt

theorem World.stack_pair {s : MachineData} {saved : Saved} {length : NatOperand} {data : Ssz.Bytes}
    {address capacity initialUsed currentUsed : BitVec 64} {writes : List (Nat × Nat)} {m : DataMem}
    (world : World s saved length data address capacity initialUsed currentUsed writes m)
    (off : Nat) (first second : BitVec 64) (inside : off + 16 ≤ 224) :
    World s saved length data address capacity initialUsed currentUsed writes
      (stackPairMem m s.regs.rsp.toBitVec off first second) := by
  exact (world.stack_store off 8 first.toInt (by omega)).stack_store (off + 8) 8 second.toInt (by omega)

theorem stack_store_regions (s : MachineData) (m : DataMem) (off count : Nat) (value : Int)
    (low : 72 ≤ s.regs.rsp.toNat) (high : s.regs.rsp.toNat + 368 ≤ 2^64)
    (inside : off + count ≤ 224) :
    RegionsFrame m (Mem.storeInt m (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) count value)
      [(workStart s, workSize)] := by
  have lowBV : 72 ≤ s.regs.rsp.toBitVec.toNat := low
  have highBV : s.regs.rsp.toBitVec.toNat + 368 ≤ 2^64 := high
  have location : (s.regs.rsp.toBitVec + BitVec.ofNat 64 off).toNat = s.regs.rsp.toNat + off := by
    change (s.regs.rsp.toBitVec + BitVec.ofNat 64 off).toNat = s.regs.rsp.toBitVec.toNat + off
    bv_omega
  apply work_store_regions
  · rw [location]
    unfold workStart
    omega
  · rw [location]
    unfold workStart workSize
    omega
  · rw [location]
    omega

theorem stack_pair_regions (s : MachineData) (m : DataMem) (off : Nat) (first second : BitVec 64)
    (low : 72 ≤ s.regs.rsp.toNat) (high : s.regs.rsp.toNat + 368 ≤ 2^64)
    (inside : off + 16 ≤ 224) :
    RegionsFrame m (stackPairMem m s.regs.rsp.toBitVec off first second) [(workStart s, workSize)] := by
  have one := stack_store_regions s m off 8 first.toInt low high (by omega)
  have two := stack_store_regions s
    (Mem.storeInt m (s.regs.rsp.toBitVec + BitVec.ofNat 64 off) 8 first.toInt)
    (off + 8) 8 second.toInt low high (by omega)
  apply (one.trans two).weaken
  intro span member
  simpa only [List.mem_append, List.mem_singleton, or_self] using member

theorem stack_pair_read (m : DataMem) (sp : BitVec 64) (off readOff count : Nat)
    (first second : BitVec 64) (high : sp.toNat + 224 ≤ 2^64)
    (inside : off + 16 ≤ 224) (readInside : readOff + count ≤ 224)
    (apart : readOff + count ≤ off ∨ off + 16 ≤ readOff) :
    Mem.loadInt (stackPairMem m sp off first second) (sp + BitVec.ofNat 64 readOff) count =
      Mem.loadInt m (sp + BitVec.ofNat 64 readOff) count := by
  unfold stackPairMem
  rw [stack_read_store _ _ readOff count (off + 8) 8 _ high readInside (by omega) (by omega)]
  exact stack_read_store _ _ readOff count off 8 _ high readInside (by omega) (by omega)

theorem stack_pair_reads (m : DataMem) (sp : BitVec 64) (off : Nat) (first second : BitVec 64)
    (high : sp.toNat + 224 ≤ 2^64) (inside : off + 16 ≤ 224) :
    Mem.loadInt (stackPairMem m sp off first second) (sp + BitVec.ofNat 64 off) 8 = some (first.toNat : Int) ∧
    Mem.loadInt (stackPairMem m sp off first second) (sp + BitVec.ofNat 64 (off + 8)) 8 = some (second.toNat : Int) := by
  constructor
  · unfold stackPairMem
    rw [stack_read_store _ _ off 8 (off + 8) 8 _ high (by omega) (by omega) (by omega)]
    exact load_store_word _ _ _
  · exact load_store_word _ _ _

theorem work_frame_operand {s : MachineData} {before after : DataMem} {address capacity used : BitVec 64}
    (frame : RegionsFrame before after [(workStart s, workSize)]) (operand : NatOperand)
    (stored : operand.At (widthLoad before)) (hp : OperandProtected s address capacity used operand) :
    operand.At (widthLoad after) := by
  apply frame.operand operand stored
  intro pointer words equal span member
  subst operand
  simp only [List.mem_singleton] at member
  subst span
  exact hp.work

end SszX86.BitVector
