import SszX86.IndicesPrefixEqualOwned
import SszX86.IndicesRejectClaimPathsArithmetic
import SszX86.IndicesStorage
import SszX86.CodecError

set_option autoImplicit false

namespace SszX86.IndicesRejectClaimPaths
open SszNative UintCodec

/-- The local activation consumes168 bytes; CALL adds8 and the actual prefix
comparator requires88. Its arguments occupy this activation's existing locals. -/
def stackBytes : Nat := 264

def Writable (s : MachineData) : Codec.Footprint :=
  fun a => Codec.InSpan a s.regs.rdi.toBitVec 68 ∨
    Codec.StackWrites s.regs.rsp.toBitVec stackBytes a

/-- This is the linked internal specialization, not the unrestricted source
API. Both source loops have had their empty-entry guards removed by IPO. -/
structure Owned (s : MachineData) (readonly : Codec.Footprint)
    (indices claims : List NatOperand) (ra : BitVec 64) : Prop where
  indicesStored : Indices.Storage.NatArrayAt s.dmem readonly s.regs.rsi.toBitVec indices
  claimsStored : Indices.Storage.NatArrayAt s.dmem readonly s.regs.rcx.toBitVec claims
  indicesCount : s.regs.rdx.toNat = indices.length
  claimsCount : s.regs.r8.toNat = claims.length
  indicesNonempty : indices ≠ []
  claimsNonempty : claims ≠ []
  resultBound : s.regs.rdi.toNat + 72 ≤ 2 ^ 64
  resultMapped : Large.Mapped s.dmem s.regs.rdi.toBitVec 68
  stack : Codec.StackAt s.dmem s.regs.rsp.toBitVec stackBytes
  returnBound : s.regs.rsp.toNat + 8 ≤ 2 ^ 64
  returnSlot : Codec.LoadAt s.dmem readonly s.regs.rsp.toBitVec 8
    (Int.ofBytes (wordBytes ra))
  resultStack : ∀ a, Codec.InSpan a s.regs.rdi.toBitVec 68 →
    ¬ Codec.StackWrites s.regs.rsp.toBitVec stackBytes a
  separate : ∀ a, readonly a → ¬ Writable s a

/-- Only the three possible validation errors inhabit this relation. Their
original represented claim operand is retained, rather than just its value. -/
def ResultAt (observe : Nat → Nat → Option Nat) (out : Nat) :
    Except SszNative.Indices.Error Unit → Prop
  | .ok () => observe (out + 64) 4 = some 0
  | .error (.notAGindex claim) => Measure.SemanticErrorAt observe out 39 claim (.small 0)
  | .error .rootHasNoBranch => Measure.SemanticErrorAt observe out 40 (.small 0) (.small 0)
  | .error (.nestedIndex claim) => Measure.SemanticErrorAt observe out 43 claim (.small 0)
  | .error _ => False

/-- Success publishes only the four-byte zero niche. Error paths publish68
meaningful bytes; neither path writes the native object's final padding. -/
def ResultWrites (out : BitVec 64) : Except SszNative.Indices.Error Unit → Codec.Footprint
  | .ok () => fun a => Codec.InSpan a (out + 64) 4
  | .error _ => fun a => Codec.InSpan a out 68

def ExactWrites (s : MachineData) (indices claims : List NatOperand) : Codec.Footprint :=
  fun a => ResultWrites s.regs.rdi.toBitVec (SszNative.Indices.rejectClaimPaths indices claims) a ∨
    Codec.StackWrites s.regs.rsp.toBitVec stackBytes a

structure Returned (s : MachineData) (readonly : Codec.Footprint)
    (indices claims : List NatOperand) (ra : BitVec 64) (t : MachineState) : Prop where
  abi : IndicesPrefixEqual.ABI s ra t
  result : ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
    (SszNative.Indices.rejectClaimPaths indices claims)
  indicesStored : Indices.Storage.NatArrayAt t.1.dmem readonly s.regs.rsi.toBitVec indices
  claimsStored : Indices.Storage.NatArrayAt t.1.dmem readonly s.regs.rcx.toBitVec claims
  readonly : ∀ a, readonly a → t.1.dmem.get? a = s.dmem.get? a
  frame : Codec.MemoryFrame s.dmem t.1.dmem (ExactWrites s indices claims)

theorem stack_budget : 168 + 8 + IndicesPrefixEqual.stackBytes = stackBytes := by
  decide

theorem Owned.comparator_stack {s : MachineData} {readonly : Codec.Footprint}
    {indices claims : List NatOperand} {ra : BitVec 64}
    (owned : Owned s readonly indices claims ra) :
    Codec.StackAt s.dmem (s.regs.rsp.toBitVec - 176) IndicesPrefixEqual.stackBytes := by
  exact owned.stack.substack 176 IndicesPrefixEqual.stackBytes (by decide)

theorem Owned.indices_count_positive {s : MachineData} {readonly : Codec.Footprint}
    {indices claims : List NatOperand} {ra : BitVec 64}
    (owned : Owned s readonly indices claims ra) : 0 < indices.length := by
  cases indices with
  | nil => exact False.elim (owned.indicesNonempty rfl)
  | cons _ _ => simp

theorem Owned.claims_count_positive {s : MachineData} {readonly : Codec.Footprint}
    {indices claims : List NatOperand} {ra : BitVec 64}
    (owned : Owned s readonly indices claims ra) : 0 < claims.length := by
  cases claims with
  | nil => exact False.elim (owned.claimsNonempty rfl)
  | cons _ _ => simp

end SszX86.IndicesRejectClaimPaths
