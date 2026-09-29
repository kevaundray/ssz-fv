import SszArm.CodecFixedMeasureInstructions

namespace SszArm.Codec.Fixed.MeasureFixed

open Dispatch.Block (next put save branch greater)
open IsFixed (loadPair)

private theorem aligned_sub160 (sp : BitVec 64) (aligned : Aligned sp 4) :
    Aligned (sp - 160#64) 4 := by
  simp only [Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at aligned ⊢
  bv_omega

private theorem aligned_add160 (sp : BitVec 64) (aligned : Aligned sp 4) :
    Aligned (sp + 160#64) 4 := by
  simp only [Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at aligned ⊢
  bv_omega

def Entry.Op.stackValue : Entry.Op → BitVec 64 → BitVec 64
  | .p0, sp => sp - 160#64
  | _, sp => sp

def Return.Op.stackValue : Return.Op → BitVec 64 → BitVec 64
  | .p640, sp | .p676, sp => sp - 16#64
  | .p672, sp | .p712, sp => sp + 16#64
  | .p736, sp => sp + 160#64
  | _, sp => sp

def Vector.Op.stackValue : Vector.Op → BitVec 64 → BitVec 64
  | .p544, sp => sp - 16#64
  | .p564, sp | .p576, sp => sp + 16#64
  | _, sp => sp

def Fields.Op.stackValue : Fields.Op → BitVec 64 → BitVec 64
  | .p380, sp => sp - 16#64
  | .p400, sp | .p412, sp => sp + 16#64
  | _, sp => sp

theorem Entry.Op.sp (op : Entry.Op) (s : ArmState) :
    r (.GPR 31#5) (op.effect s) = op.stackValue (r (.GPR 31#5) s) := by
  cases op <;> simp [Entry.Op.effect, Entry.Op.stackValue, next, put, save, branch,
    loadPair, Udivti3.compare, Udivti3.next, state_simp_rules]

theorem Return.Op.sp (op : Return.Op) (s : ArmState) :
    r (.GPR 31#5) (op.effect s) = op.stackValue (r (.GPR 31#5) s) := by
  cases op <;> simp [Return.Op.effect, Return.Op.stackValue, next, put, loadPair, state_simp_rules]

theorem Vector.Op.sp (op : Vector.Op) (s : ArmState) :
    r (.GPR 31#5) (op.effect s) = op.stackValue (r (.GPR 31#5) s) := by
  cases op <;> simp [Vector.Op.effect, Vector.Op.stackValue, next, put, branch,
    loadPair, load32, storePair, storePair32, call, state_simp_rules]

theorem Bits.Op.sp (op : Bits.Op) (s : ArmState) :
    r (.GPR 31#5) (op.effect s) = r (.GPR 31#5) s := by
  cases op <;> simp [Bits.Op.effect, next, put, branch,
    loadPair, load32, storePair, storePair32, call, state_simp_rules]

theorem Fields.Op.sp (op : Fields.Op) (s : ArmState) :
    r (.GPR 31#5) (op.effect s) = op.stackValue (r (.GPR 31#5) s) := by
  cases op <;> simp [Fields.Op.effect, Fields.Op.stackValue, next, put, branch,
    loadPair, load32, storePair, storePair32, call, Udivti3.compare, Udivti3.next, state_simp_rules]

theorem Entry.Op.stack_aligned (op : Entry.Op) (sp : BitVec 64) (aligned : Aligned sp 4) :
    Aligned (op.stackValue sp) 4 := by
  cases op <;> simp only [Entry.Op.stackValue]
  case p0 => exact aligned_sub160 sp aligned
  all_goals exact aligned

theorem Return.Op.stack_aligned (op : Return.Op) (sp : BitVec 64) (aligned : Aligned sp 4) :
    Aligned (op.stackValue sp) 4 := by
  cases op <;> simp only [Return.Op.stackValue]
  case p640 | p676 => exact BoolCodec.aligned_sub16 sp aligned
  case p672 | p712 => exact BoolCodec.aligned_add16 sp aligned
  case p736 => exact aligned_add160 sp aligned
  all_goals exact aligned

theorem Vector.Op.stack_aligned (op : Vector.Op) (sp : BitVec 64) (aligned : Aligned sp 4) :
    Aligned (op.stackValue sp) 4 := by
  cases op <;> simp only [Vector.Op.stackValue]
  case p544 => exact BoolCodec.aligned_sub16 sp aligned
  case p564 | p576 => exact BoolCodec.aligned_add16 sp aligned
  all_goals exact aligned

theorem Fields.Op.stack_aligned (op : Fields.Op) (sp : BitVec 64) (aligned : Aligned sp 4) :
    Aligned (op.stackValue sp) 4 := by
  cases op <;> simp only [Fields.Op.stackValue]
  case p380 => exact BoolCodec.aligned_sub16 sp aligned
  case p400 | p412 => exact BoolCodec.aligned_add16 sp aligned
  all_goals exact aligned

theorem Op.aligned (op : Op) (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (op.effect s) := by
  have original := BoolCodec.stack_aligned s aligned
  cases op with
  | entry op => exact CheckSPAlignment_of_r_sp_aligned (op.sp s) (op.stack_aligned _ original)
  | finish op => exact CheckSPAlignment_of_r_sp_aligned (op.sp s) (op.stack_aligned _ original)
  | vector op => exact CheckSPAlignment_of_r_sp_aligned (op.sp s) (op.stack_aligned _ original)
  | bits op => exact CheckSPAlignment_of_r_sp_aligned (op.sp s) original
  | fields op => exact CheckSPAlignment_of_r_sp_aligned (op.sp s) (op.stack_aligned _ original)

theorem block_aligned (ops : List Op) (s : ArmState) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (block ops s) := by
  induction ops generalizing s with
  | nil => exact aligned
  | cons op ops ih => exact ih _ (op.aligned s aligned)

def PCs (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧ PCs base ops (op.effect s)

theorem PCs.follows {base : BitVec 64} {ops : List Op} {s : ArmState}
    (pcs : PCs base ops s) (aligned : CheckSPAlignment s) : Follows base ops s := by
  induction ops generalizing s with
  | nil => trivial
  | cons op ops ih => exact ⟨aligned, pcs.1, ih pcs.2 (op.aligned s aligned)⟩

theorem run_block (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : Linked.MeasureFixed.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pcs : PCs base ops s) :
    run ops.length s = block ops s := block_run ops s base code error (pcs.follows aligned)

end SszArm.Codec.Fixed.MeasureFixed
