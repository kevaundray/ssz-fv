import SszX86.CodecStack
import SszX86.IndicesPrefixEqualArithmetic

set_option autoImplicit false

namespace SszX86.IndicesPrefixEqual
open SszNative UintCodec

/-- Six saved registers, twenty-four local bytes, and the real lowered BSR's
sixteen-byte spill area. The original return slot is outside this footprint. -/
def stackBytes : Nat := 88

def Writable (s : MachineData) : Codec.Footprint :=
  Codec.StackWrites s.regs.rsp.toBitVec stackBytes

/-- Original SysV entry observations. The right Nat's payload is the first
stack argument; the u128 right shift starts after its alignment gap. No gap or
padding byte is assumed initialized, and borrowed limb slices may alias. -/
structure Owned (s : MachineData) (readonly : Codec.Footprint)
    (left : NatOperand) (leftShift : Nat) (flip : Bool)
    (right : NatOperand) (rightShift : Nat) (ra : BitVec 64) : Prop where
  leftPointer : s.regs.rdi.toBitVec = left.pointer
  leftPayload : s.regs.rsi.toBitVec = left.payload
  leftStored : left.At (widthLoad s.dmem)
  leftBorrowed : ∀ a, Emit.NatBorrowed left a → readonly a
  leftShiftValue : leftShift = s.regs.rdx.toNat + 2 ^ 64 * s.regs.rcx.toNat
  flipValue : s.regs.r8.toBitVec.setWidth 8 = BitVec.ofNat 8 (if flip then 1 else 0)
  rightPointer : s.regs.r9.toBitVec = right.pointer
  rightPayload : Codec.LoadAt s.dmem readonly (s.regs.rsp.toBitVec + 8) 8
    (right.payload.toNat : Int)
  rightStored : right.At (widthLoad s.dmem)
  rightBorrowed : ∀ a, Emit.NatBorrowed right a → readonly a
  rightShiftBound : rightShift < 2 ^ 128
  rightShiftLow : Codec.LoadAt s.dmem readonly (s.regs.rsp.toBitVec + 24) 8
    ((BitVec.ofNat 64 rightShift).toNat : Int)
  rightShiftHigh : Codec.LoadAt s.dmem readonly (s.regs.rsp.toBitVec + 32) 8
    ((BitVec.ofNat 64 (rightShift / 2 ^ 64)).toNat : Int)
  argumentsBound : s.regs.rsp.toNat + 40 ≤ 2 ^ 64
  stack : Codec.StackAt s.dmem s.regs.rsp.toBitVec stackBytes
  returnSlot : Codec.LoadAt s.dmem readonly s.regs.rsp.toBitVec 8
    (Int.ofBytes (wordBytes ra))
  separate : ∀ a, readonly a → ¬ Writable s a

/-- Physical count bounds are consequences of the original limb-storage
relation, including Small zero and an empty or zero-padded Large operand. -/
theorem operand_count_bound (m : DataMem) (operand : NatOperand)
    (stored : operand.At (widthLoad m)) : operand.words.length < 2 ^ 64 := by
  cases operand with
  | small word => change 1 < 2 ^ 64; decide
  | large pointer words =>
      have bound := stored.2.2.1
      change words.length < 2 ^ 64
      omega

theorem Owned.left_count_bound {s : MachineData} {readonly : Codec.Footprint}
    {left : NatOperand} {leftShift : Nat} {flip : Bool}
    {right : NatOperand} {rightShift : Nat} {ra : BitVec 64}
    (owned : Owned s readonly left leftShift flip right rightShift ra) :
    left.words.length < 2 ^ 64 :=
  operand_count_bound s.dmem left owned.leftStored

theorem Owned.right_count_bound {s : MachineData} {readonly : Codec.Footprint}
    {left : NatOperand} {leftShift : Nat} {flip : Bool}
    {right : NatOperand} {rightShift : Nat} {ra : BitVec 64}
    (owned : Owned s readonly left leftShift flip right rightShift ra) :
    right.words.length < 2 ^ 64 :=
  operand_count_bound s.dmem right owned.rightStored

/-- Frame transport of register-passed operands uses precisely the limb bytes
covered by the existing codec storage convention, not a fabricated Nat header. -/
theorem operand_frame (m n : DataMem) (writes : Codec.Footprint)
    (frame : Codec.MemoryFrame m n writes) (operand : NatOperand)
    (separate : ∀ a, Emit.NatBorrowed operand a → ¬ writes a)
    (stored : operand.At (widthLoad m)) : operand.At (widthLoad n) := by
  cases operand with
  | small word => trivial
  | large pointer words =>
      obtain ⟨positive, aligned, bound, observations⟩ := stored
      refine ⟨positive, aligned, bound, ?_⟩
      intro i
      have same : widthLoad n (pointer.toNat + 8 * i.val) 8 =
          widthLoad m (pointer.toNat + 8 * i.val) 8 := by
        unfold widthLoad
        rw [width_address]
        congr 1
        apply Emit.frame_load m n writes frame
        intro j inside
        apply separate
        exact Emit.span_shift pointer (8 * i.val) 8 (8 * words.length)
          (by have := i.isLt; omega) ⟨j, inside, rfl⟩
      rw [same]
      exact observations i

structure ABI (s : MachineData) (ra : BitVec 64) (t : MachineState) : Prop where
  returned : t.2 = Int64.ofBitVec ra
  stack : t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8
  rbx : t.1.regs.rbx = s.regs.rbx
  rbp : t.1.regs.rbp = s.regs.rbp
  r12 : t.1.regs.r12 = s.regs.r12
  r13 : t.1.regs.r13 = s.regs.r13
  r14 : t.1.regs.r14 = s.regs.r14
  r15 : t.1.regs.r15 = s.regs.r15
  vectors : t.1.zmms = s.zmms

structure Returned (s : MachineData) (readonly : Codec.Footprint)
    (left : NatOperand) (leftShift : Nat) (flip : Bool)
    (right : NatOperand) (rightShift : Nat) (ra : BitVec 64)
    (t : MachineState) : Prop where
  abi : ABI s ra t
  result : t.1.regs.rax.toBitVec.setWidth 8 = BitVec.ofNat 8
    (if SszNative.Indices.prefixEqual left leftShift flip right rightShift then 1 else 0)
  leftStored : left.At (widthLoad t.1.dmem)
  rightStored : right.At (widthLoad t.1.dmem)
  readonly : ∀ a, readonly a → t.1.dmem.get? a = s.dmem.get? a
  frame : Codec.MemoryFrame s.dmem t.1.dmem (Writable s)

end SszX86.IndicesPrefixEqual
