import SszArm.DelimitedContract
import SszNatAdd
import SszNatArithmeticMemory

namespace SszArm.NatAdd

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame Returned)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The actual ABI passes the three-word arena descriptor in X5. -/
def arenaOf (s : ArmState) : SszNative.Delimited.ArenaState :=
  ⟨(read_mem_bytes 8 (r (.GPR 5#5) s) s).toNat,
   (read_mem_bytes 8 (r (.GPR 5#5) s + 8#64) s).toNat,
   (read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) s).toNat⟩

/-- The frozen shared native algorithm, with the original physical arena words. -/
def outcome (s : ArmState) (left right : SszNative.NatOperand) :
    SszNative.NatArithmetic.Outcome SszNative.NatOperand :=
  SszNative.NatAdd.run left right (arenaOf s).base (arenaOf s).capacity (arenaOf s).used

/-- The leaf writes its 68-byte result and at most two lowering spills. -/
def localWrites (s : ArmState) : List Span :=
  [((r (.GPR 0#5) s).toNat, 68), ((r (.GPR 31#5) s).toNat - 16, 16)]

/-- Allocation adds only the cursor and the complete written limb extent.
Neither alignment padding nor the used arena prefix is writable. -/
def writesFor (s : ArmState)
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand) : List Span :=
  match result.allocation with
  | none => localWrites s
  | some reservation => localWrites s ++
      [((r (.GPR 5#5) s).toNat + 16, 8), (reservation.pointer, 8 * result.written.length)]

/-- Borrowed operands retain their exact original extent, including redundant
high zero limbs. Small and empty Large operands require no borrowed bytes. -/
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

/-- A physical frame preserves the exact supplied limbs, not just their value. -/
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

/-- Scratch observations cover every allocated written word, including a
redundant high zero even when the returned representation has trimmed it. -/
def WrittenAt (observe : Nat → Nat → Option Nat)
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand) : Prop :=
  ∀ reservation, result.allocation = some reservation →
    SszNative.NatMemory.wordsAt observe reservation.pointer result.written

theorem local_frame {s t : ArmState}
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand)
    (frame : MemoryFrame (localWrites s) s t) : MemoryFrame (writesFor s result) s t := by
  apply frame.weaken
  intro span member
  cases allocated : result.allocation <;> simp_all [writesFor]

end SszArm.NatAdd
