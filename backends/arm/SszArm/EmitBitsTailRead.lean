import SszArm.EmitBitsTailOps
import SszArm.EmitBitsQuotient

namespace SszArm.Emit.Bits

open Activation (put)

def Path.readStart : Path → Nat
  | .list => 668 | .vector => 1276

def Path.readOps : Path → List Tail.Op
  | .list => [.p668, .p672, .p676, .p680, .p684, .p688, .p692]
  | .vector => [.p1276, .p1280, .p1284, .p1288, .p1292, .p1296, .p1300]

@[irreducible] def byteLoaded (s : ArmState) : ArmState :=
  w .PC (read_pc s + 28#64)
    (w (.GPR 8#5) ((read_mem_bytes 1 (r (.GPR 22#5) s + r (.GPR 23#5) s)
      (NatCompare.saved s 9#5)).setWidth 64) (NatCompare.saved s 9#5))

theorem byte_read_follows (path : Path) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 path.readStart) :
    Tail.Follows base path.readOps s := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  cases path <;>
    simp (config := {decide := true, instances := true})
      [Path.readOps, Path.readStart, Tail.Follows, Tail.Op.row, Tail.Op.effect,
       Activation.put, Activation.next, Dispatch.next, state_simp_rules,
       aligned, stack, lower, CheckSPAlignment, pc, BitVec.add_assoc,
       BitVec.sub_add_cancel]

theorem byte_read_effect (path : Path) (s : ArmState)
    (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat) :
    Tail.block path.readOps s = byteLoaded s := by
  have restored : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (NatCompare.saved s 9#5) =
      r (.GPR 9#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have fields := NatAdd.load_restore_fields (NatCompare.saved s 9#5) 9#5 8#5
    (r (.GPR 22#5) s + r (.GPR 23#5) s)
    ((read_mem_bytes 1 (r (.GPR 22#5) s + r (.GPR 23#5) s)
      (NatCompare.saved s 9#5)).setWidth 64)
    (by decide) (by decide) (by decide)
  simp only [NatCompare.saved, r_of_write_mem_bytes] at restored fields
  cases path <;>
    simpa (config := {decide := true})
      [Tail.block, Path.readOps, Tail.Op.effect, Activation.put, Activation.next,
       Dispatch.next, byteLoaded, NatCompare.saved, NatAdd.load_store_field,
       NatAdd.load_gpr_pc, state_simp_rules, BitVec.add_assoc, BitVec.sub_add_cancel,
       restored] using congrArg (w .PC (read_pc s + 28#64)) fields

theorem byte_read_run (path : Path) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 path.readStart)
    (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat) :
    run 7 s = byteLoaded s := by
  rw [show 7 = path.readOps.length by cases path <;> rfl,
    Tail.runs path.readOps s base code error (byte_read_follows path s base aligned pc)]
  exact byte_read_effect path s stackLow

@[simp] theorem byteLoaded_pc (s : ArmState) : read_pc (byteLoaded s) = read_pc s + 28#64 := by
  simp [byteLoaded, state_simp_rules]

@[simp] theorem byteLoaded_program (s : ArmState) : (byteLoaded s).program = s.program := by
  simp [byteLoaded, NatCompare.saved, state_simp_rules]

@[simp] theorem byteLoaded_error (s : ArmState) : read_err (byteLoaded s) = read_err s := by
  simp [byteLoaded, NatCompare.saved, state_simp_rules]

@[simp] theorem byteLoaded_register (s : ArmState) (reg : BitVec 5) (other : reg ≠ 8#5) :
    r (.GPR reg) (byteLoaded s) = r (.GPR reg) s := by
  simp [byteLoaded, NatCompare.saved, state_simp_rules, other]

@[simp] theorem byteLoaded_byte (s : ArmState) :
    r (.GPR 8#5) (byteLoaded s) =
      (read_mem_bytes 1 (r (.GPR 22#5) s + r (.GPR 23#5) s) (NatCompare.saved s 9#5)).setWidth 64 := by
  simp [byteLoaded, state_simp_rules]

@[simp] theorem byteLoaded_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (byteLoaded s) = r (.SFP reg) s := by
  simp [byteLoaded, NatCompare.saved, state_simp_rules]

end SszArm.Emit.Bits
