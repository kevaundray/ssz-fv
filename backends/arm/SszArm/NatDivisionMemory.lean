import SszArm.DelimitedContract
import SszNatDivision
import SszNatArithmeticMemory

namespace SszArm.NatDivision

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame Returned)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The division ABI passes the three-word arena descriptor in X4. -/
def arenaOf (s : ArmState) : SszNative.Delimited.ArenaState :=
  ⟨(read_mem_bytes 8 (r (.GPR 4#5) s) s).toNat,
   (read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s).toNat,
   (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) s).toNat⟩

/-- The frozen native algorithm, using the original divisor and arena words. -/
def outcome (s : ArmState) (operand : SszNative.NatOperand) :
    SszNative.NatArithmetic.Outcome (SszNative.NatOperand × BitVec 64) :=
  SszNative.NatDivision.run operand (r (.GPR 3#5) s)
    (arenaOf s).base (arenaOf s).capacity (arenaOf s).used

/-- The 68-byte result and the complete activation: 64 saved bytes and the
additional 16-byte lowering spill below the adjusted stack pointer. -/
def localWrites (s : ArmState) : List Span :=
  [((r (.GPR 0#5) s).toNat, 68), ((r (.GPR 31#5) s).toNat - 80, 80)]

/-- Allocation permits exactly the cursor word and every written quotient limb.
Alignment padding and the already-used arena prefix are not writable. -/
def writesFor (s : ArmState)
    (result : SszNative.NatArithmetic.Outcome (SszNative.NatOperand × BitVec 64)) :
    List Span :=
  match result.allocation with
  | none => localWrites s
  | some reservation => localWrites s ++
      [((r (.GPR 4#5) s).toNat + 16, 8), (reservation.pointer, 8 * result.written.length)]

/-- Ownership covers the exact original limb list, including redundant high
zeros. Empty Large operands and Small operands borrow no bytes. -/
def OperandOwned (writes : List Span) : SszNative.NatOperand → Prop
  | .small _ => True
  | .large pointer words => Protected writes pointer.toNat (8 * words.length)

def OperandBytesPreserved (s t : ArmState) : SszNative.NatOperand → Prop
  | .small _ => True
  | .large pointer words => ∀ a : BitVec 64, pointer.toNat ≤ a.toNat →
      a.toNat < pointer.toNat + 8 * words.length → t.mem a = s.mem a

structure OperandPreserved (s t : ArmState) (operand : SszNative.NatOperand) : Prop where
  representation : operand.At (widthLoad t)
  bytes : OperandBytesPreserved s t operand

/-- A byte frame retains the supplied representation, not just its value. -/
theorem operand_at_preserved {writes : List Span} {s t : ArmState}
    (frame : MemoryFrame writes s t) (operand : SszNative.NatOperand)
    (input : operand.At (widthLoad s)) (owned : OperandOwned writes operand) :
    operand.At (widthLoad t) := by
  cases operand with
  | small word => trivial
  | large pointer words =>
    obtain ⟨positive, aligned, physical, limbs⟩ := input
    refine ⟨positive, aligned, physical, ?_⟩
    intro i
    have hi := i.isLt
    have protectedInput : Protected writes pointer.toNat (8 * words.length) := owned
    have wordOwned : Protected writes (pointer.toNat + 8 * i.val) 8 :=
      protectedInput.subspan (8 * i.val) 8 (by omega)
    rw [frame.load _ _ (by omega) wordOwned]
    exact limbs i

theorem operand_preserved {writes : List Span} {s t : ArmState}
    (frame : MemoryFrame writes s t) (operand : SszNative.NatOperand)
    (input : operand.At (widthLoad s)) (owned : OperandOwned writes operand) :
    OperandPreserved s t operand := by
  refine ⟨operand_at_preserved frame operand input owned, ?_⟩
  cases operand with
  | small word => trivial
  | large pointer words =>
    intro a low high
    exact frame.protected_byte owned a low high

/-- Observe all physically written words independently of the result payload.
In division the payload is a quotient/remainder pair; normalization of its
quotient never shortens this scratch observation. -/
def WrittenAt {α : Type} (observe : Nat → Nat → Option Nat)
    (result : SszNative.NatArithmetic.Outcome α) : Prop :=
  ∀ reservation, result.allocation = some reservation →
    SszNative.NatMemory.wordsAt observe reservation.pointer result.written

theorem WrittenAt.none {α : Type} (observe : Nat → Nat → Option Nat)
    (result : SszNative.NatArithmetic.Outcome α) (unallocated : result.allocation = none) :
    WrittenAt observe result := by
  intro reservation allocated
  rw [unallocated] at allocated
  cases allocated

theorem local_frame {s t : ArmState}
    (result : SszNative.NatArithmetic.Outcome (SszNative.NatOperand × BitVec 64))
    (frame : MemoryFrame (localWrites s) s t) : MemoryFrame (writesFor s result) s t := by
  apply frame.weaken
  intro span member
  cases allocated : result.allocation <;> simp_all [writesFor]

end SszArm.NatDivision
