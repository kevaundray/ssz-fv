import SszArm.CodecFixedExec
import SszArm.BitVectorMemory

namespace SszArm.Codec.Fixed.IsFixed

open Dispatch.Block (next put save branch greater)
open Delimited (MemoryFrame Span)

private theorem aligned_sub32 (x : BitVec 64) (aligned : Aligned x 4) :
    Aligned (x - 32#64) 4 := by
  have twice := BoolCodec.aligned_sub16 _ (BoolCodec.aligned_sub16 x aligned)
  simpa only [BitVec.sub_sub, show 16#64 + 16#64 = 32#64 from rfl] using twice

private theorem aligned_add32 (x : BitVec 64) (aligned : Aligned x 4) :
    Aligned (x + 32#64) 4 := by
  have twice := BoolCodec.aligned_add16 _ (BoolCodec.aligned_add16 x aligned)
  simpa only [BitVec.add_assoc, show 16#64 + 16#64 = 32#64 from rfl] using twice

def Op.stackPointer (op : Op) (sp : BitVec 64) : BitVec 64 :=
  match op with
  | .p0 => sp - 32#64
  | .p132 => sp - 16#64
  | .p152 | .p164 => sp + 16#64
  | .p180 | .p196 => sp + 32#64
  | _ => sp

theorem Op.sp (op : Op) (s : ArmState) :
    r (.GPR 31#5) (op.effect s) = op.stackPointer (r (.GPR 31#5) s) := by
  cases op <;>
    simp (config := {decide := true}) [Op.effect, Op.stackPointer, next, put, save,
      branch, loadPair, restore, Udivti3.compare, Udivti3.next, state_simp_rules]

theorem Op.stackPointer_aligned (op : Op) (sp : BitVec 64) (aligned : Aligned sp 4) :
    Aligned (op.stackPointer sp) 4 := by
  cases op <;> simp only [Op.stackPointer]
  case p0 => exact aligned_sub32 sp aligned
  case p132 => exact BoolCodec.aligned_sub16 sp aligned
  case p152 | p164 => exact BoolCodec.aligned_add16 sp aligned
  case p180 | p196 => exact aligned_add32 sp aligned
  all_goals exact aligned

theorem Op.aligned (op : Op) (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (op.effect s) :=
  CheckSPAlignment_of_r_sp_aligned (op.sp s)
    (op.stackPointer_aligned _ (BoolCodec.stack_aligned s aligned))

theorem block_aligned (ops : List Op) (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (block ops s) := by
  induction ops generalizing s with
  | nil => exact aligned
  | cons op ops ih => exact ih _ (op.aligned s aligned)

/-- Only these three actual instructions write memory. -/
def Op.writes : Op → ArmState → List Span
  | .p4, s | .p136, s => [((r (.GPR 31#5) s).toNat, 8)]
  | .p8, s => [((r (.GPR 31#5) s + 16#64).toNat, 16)]
  | _, _ => []

theorem Op.memory_frame (op : Op) (s : ArmState)
    (physical : ∀ span ∈ op.writes s, span.1 + span.2 ≤ 2^64) :
    MemoryFrame (op.writes s) s (op.effect s) := by
  cases op
  case p4 =>
    simpa only [MemoryFrame, Op.writes, Op.effect, next, state_simp_rules] using
      Delimited.store_frame s (r (.GPR 31#5) s) 8 (r (.GPR 30#5) s)
        (physical ((r (.GPR 31#5) s).toNat, 8) (by simp [Op.writes]))
  case p8 =>
    simpa only [MemoryFrame, Op.writes, Op.effect, save, next, state_simp_rules] using
      Delimited.store_frame s (r (.GPR 31#5) s + 16#64) 16
        (r (.GPR 19) s ++ r (.GPR 20) s)
        (physical ((r (.GPR 31#5) s + 16#64).toNat, 16) (by simp [Op.writes]))
  case p136 =>
    simpa only [MemoryFrame, Op.writes, Op.effect, next, state_simp_rules] using
      Delimited.store_frame s (r (.GPR 31#5) s) 8 (r (.GPR 9#5) s)
        (physical ((r (.GPR 31#5) s).toNat, 8) (by simp [Op.writes]))
  all_goals
    intro address outside
    simp [Op.effect, next, put, branch, loadPair, restore,
      Udivti3.compare, Udivti3.next, state_simp_rules]

theorem Op.register (op : Op) (s : ArmState) (reg : BitVec 5)
    (preserved : reg ≠ 0#5 ∧ reg ≠ 8#5 ∧ reg ≠ 9#5 ∧ reg ≠ 19#5 ∧
      reg ≠ 20#5 ∧ reg ≠ 30#5 ∧ reg ≠ 31#5) :
    r (.GPR reg) (op.effect s) = r (.GPR reg) s := by
  rcases preserved with ⟨h0, h8, h9, h19, h20, h30, h31⟩
  cases op <;> simp [Op.effect, next, put, save, branch, loadPair, restore,
    Udivti3.compare, Udivti3.next, state_simp_rules, h0, h8, h9, h19, h20, h30, h31]

theorem block_register (ops : List Op) (s : ArmState) (reg : BitVec 5)
    (preserved : reg ≠ 0#5 ∧ reg ≠ 8#5 ∧ reg ≠ 9#5 ∧ reg ≠ 19#5 ∧
      reg ≠ 20#5 ∧ reg ≠ 30#5 ∧ reg ≠ 31#5) :
    r (.GPR reg) (block ops s) = r (.GPR reg) s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.register s reg preserved)

/-- Finite instruction blocks transport a caller's exact writable envelope. -/
def StoresWithin (writes : List Span) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s =>
      (∀ span ∈ op.writes s, span.1 + span.2 ≤ 2^64) ∧
      BitVector.Covers writes (op.writes s) ∧ StoresWithin writes ops (op.effect s)

theorem block_frame (ops : List Op) (s : ArmState) (writes : List Span)
    (within : StoresWithin writes ops s) : MemoryFrame writes s (block ops s) := by
  induction ops generalizing s with
  | nil => exact MemoryFrame.refl _ _
  | cons op ops ih =>
    exact (within.2.1.frame (op.memory_frame s within.1)).trans (ih _ within.2.2)

end SszArm.Codec.Fixed.IsFixed
