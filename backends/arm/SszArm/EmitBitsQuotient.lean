import SszArm.EmitBitsOps
import SszArm.NatAddLoadState
import SszArm.EmitBitsFacts

namespace SszArm.Emit.Bits

open Activation (put)
open Dispatch (next)

inductive Path where
  | list | vector
  deriving DecidableEq

def Path.shiftStart : Path → Nat
  | .list => 584 | .vector => 1192

def Path.low : Path → BitVec 5
  | .list => 26 | .vector => 25

def Path.shiftOps : Path → List Op
  | .list => [.p584, .p588, .p592, .p596, .p600, .p604]
  | .vector => [.p1192, .p1196, .p1200, .p1204, .p1208, .p1212]

@[irreducible] def shifted (path : Path) (s : ArmState) : ArmState :=
  w .PC (read_pc s + 24#64)
    (w (.GPR 23#5) ((r (.GPR path.low) s >>> (3 : Nat)) |||
      (r (.GPR 8#5) s <<< (61 : Nat))) (NatCompare.saved s 9#5))

theorem shift_follows (path : Path) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 path.shiftStart) :
    Follows base path.shiftOps s := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  cases path <;>
    simp (config := {decide := true, instances := true})
      [Path.shiftOps, Path.shiftStart, Follows, Op.row, Op.effect,
       Activation.put, Activation.next, Dispatch.next, state_simp_rules,
       aligned, stack, lower, CheckSPAlignment, pc, BitVec.add_assoc,
       BitVec.sub_add_cancel]

theorem shift_effect (path : Path) (s : ArmState)
    (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat) :
    block path.shiftOps s = shifted path s := by
  have restored : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (NatCompare.saved s 9#5) =
      r (.GPR 9#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have fields := NatAdd.load_restore_fields (NatCompare.saved s 9#5) 9#5 23#5
    (r (.GPR path.low) s >>> (3 : Nat))
    ((r (.GPR path.low) s >>> (3 : Nat)) ||| (r (.GPR 8#5) s <<< (61 : Nat)))
    (by decide) (by decide) (by decide)
  simp only [NatCompare.saved, r_of_write_mem_bytes] at restored fields
  cases path <;>
    simpa (config := {decide := true})
      [block, Path.shiftOps, Path.low, Op.effect, Activation.put, Activation.next,
       Dispatch.next, shifted, NatCompare.saved, NatAdd.load_store_field,
       NatAdd.load_gpr_pc, state_simp_rules, BitVec.add_assoc, BitVec.sub_add_cancel,
       restored] using congrArg (w .PC (read_pc s + 24#64)) fields

theorem shift_run (path : Path) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 path.shiftStart)
    (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat) :
    run 6 s = shifted path s := by
  rw [show 6 = path.shiftOps.length by cases path <;> rfl,
    runs path.shiftOps s base code error (shift_follows path s base aligned pc)]
  exact shift_effect path s stackLow

@[simp] theorem shifted_pc (path : Path) (s : ArmState) :
    read_pc (shifted path s) = read_pc s + 24#64 := by
  simp [shifted, state_simp_rules]

@[simp] theorem shifted_program (path : Path) (s : ArmState) :
    (shifted path s).program = s.program := by
  simp [shifted, NatCompare.saved, state_simp_rules]

@[simp] theorem shifted_error (path : Path) (s : ArmState) :
    read_err (shifted path s) = read_err s := by
  simp [shifted, NatCompare.saved, state_simp_rules]

@[simp] theorem shifted_register (path : Path) (s : ArmState) (reg : BitVec 5)
    (other : reg ≠ 23#5) : r (.GPR reg) (shifted path s) = r (.GPR reg) s := by
  simp [shifted, NatCompare.saved, state_simp_rules, other]

@[simp] theorem shifted_quotient (path : Path) (s : ArmState) :
    r (.GPR 23#5) (shifted path s) =
      (r (.GPR path.low) s >>> (3 : Nat)) ||| (r (.GPR 8#5) s <<< (61 : Nat)) := by
  simp [shifted, state_simp_rules]

@[simp] theorem shifted_vector (path : Path) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (shifted path s) = r (.SFP reg) s := by
  simp [shifted, NatCompare.saved, state_simp_rules]

end SszArm.Emit.Bits
