import SszArm.EmitBitsTailRead
import SszArm.EmitBitsEntry
import SszArm.NatAddLoopMemory

namespace SszArm.Emit.Bits

open Delimited (MemoryFrame Protected)
open SszNative.Serialize (Desc Value)

def Path.storeStart : Path → Nat
  | .list => 1496 | .vector => 1332

def Path.storeOps : Path → List Tail.Op
  | .list => [.p1496, .p1500, .p1504, .p1508, .p1512, .p1516, .p1520]
  | .vector => [.p1332, .p1336, .p1340, .p1344, .p1348, .p1352, .p1356]

def storeAddress (s : ArmState) : BitVec 64 := r (.GPR 20#5) s + r (.GPR 23#5) s

def storeMemory (s : ArmState) : ArmState :=
  write_mem_bytes 1 (storeAddress s) ((r (.GPR 8#5) s).setWidth 8) (NatCompare.saved s 9#5)

@[irreducible] def byteStored (s : ArmState) : ArmState := w .PC (read_pc s + 28#64) (storeMemory s)

theorem store_effect (path : Path) (s : ArmState)
    (restore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (storeMemory s) = r (.GPR 9#5) s) :
    Tail.block path.storeOps s = byteStored s := by
  have restored := NatAdd.store_restore_fields (storeMemory s) 9#5 (storeAddress s) (by decide)
  simp only [storeMemory, storeAddress, NatCompare.saved, r_of_write_mem_bytes] at restore restored
  cases path <;>
    simpa (config := {decide := true})
      [Tail.block, Path.storeOps, Tail.Op.effect, storeAddress, byteStored, storeMemory,
       NatCompare.saved, Activation.put, Activation.next, Dispatch.next,
       NatAdd.load_store_field, NatAdd.load_gpr_pc, state_simp_rules,
       BitVec.add_assoc, BitVec.sub_add_cancel, restore] using
      congrArg (w .PC (read_pc s + 28#64)) restored

theorem store_follows (path : Path) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 path.storeStart) :
    Tail.Follows base path.storeOps s := by
  change r .PC s = _ at pc
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  cases path <;>
    simp (config := {decide := true, instances := true})
      [Path.storeOps, Path.storeStart, Tail.Follows, Tail.Op.row, Tail.Op.effect,
       Activation.put, Activation.next, Dispatch.next, state_simp_rules,
       aligned, stack, lower, CheckSPAlignment, pc, BitVec.add_assoc, BitVec.sub_add_cancel]

theorem store_position {s : ArmState} {args : Args} {desc : Desc} {value : Value} {size : Nat}
    (owned : Owned s args desc value size) (output : r (.GPR 20#5) s = args.output)
    (inside : (r (.GPR 23#5) s).toNat < size) :
    (storeAddress s).toNat = args.output.toNat + (r (.GPR 23#5) s).toNat := by
  have fitting := owned.fitting
  have bound := owned.outputBound
  simp only [storeAddress, output]
  bv_omega

/-- The spill reload is derived from the original live-output/stack separation.
No reload observation or post-helper ownership is a caller assumption. -/
theorem store_restore {s : ArmState} {args : Args} {desc : Desc} {value : Value} {size : Nat}
    (owned : Owned s args desc value size) (output : r (.GPR 20#5) s = args.output)
    (stack : r (.GPR 31#5) s = args.bodySP) (inside : (r (.GPR 23#5) s).toNat < size) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (storeMemory s) = r (.GPR 9#5) s := by
  have position := store_position owned output inside
  have low := owned.stackLow
  have capacity := owned.fitting
  have bounded := owned.outputBound
  have stackBound := args.stack.isLt
  have slot : (r (.GPR 31#5) s - 16#64).toNat = args.stack.toNat - 176 := by
    rw [stack, Args.bodySP]
    bv_omega
  have apart : Protected [((storeAddress s).toNat, 1)]
      (r (.GPR 31#5) s - 16#64).toNat 8 := by
    right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    rcases owned.outputStack with empty | separate
    · omega
    · have separated := separate (args.stack.toNat - 176, 16) (by simp [stackWrites])
      simp only [Prod.fst, Prod.snd] at separated ⊢
      rw [slot, position]
      omega
  unfold storeMemory
  rw [(Delimited.store_frame (NatCompare.saved s 9#5) (storeAddress s) 1
    ((r (.GPR 8#5) s).setWidth 8) (by rw [position]; omega)).read _ 8 (by rw [slot]; omega) apart]
  exact BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by rw [slot]; omega)

theorem store_run {s : ArmState} {args : Args} {desc : Desc} {value : Value} {size : Nat}
    (path : Path) (base : BitVec 64) (owned : Owned s args desc value size)
    (output : r (.GPR 20#5) s = args.output) (stack : r (.GPR 31#5) s = args.bodySP)
    (inside : (r (.GPR 23#5) s).toNat < size)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 path.storeStart) :
    run 7 s = byteStored s := by
  rw [show 7 = path.storeOps.length by cases path <;> rfl,
    Tail.runs path.storeOps s base code error (store_follows path s base aligned pc)]
  exact store_effect path s (store_restore owned output stack inside)

@[simp] theorem byteStored_program (s : ArmState) : (byteStored s).program = s.program := by
  simp [byteStored, storeMemory, NatCompare.saved, state_simp_rules]

@[simp] theorem byteStored_error (s : ArmState) : read_err (byteStored s) = read_err s := by
  simp [byteStored, storeMemory, NatCompare.saved, state_simp_rules]

@[simp] theorem byteStored_pc (s : ArmState) : read_pc (byteStored s) = read_pc s + 28#64 := by
  simp [byteStored, state_simp_rules]

@[simp] theorem byteStored_register (s : ArmState) (reg : BitVec 5) :
    r (.GPR reg) (byteStored s) = r (.GPR reg) s := by
  simp [byteStored, storeMemory, NatCompare.saved, state_simp_rules]

@[simp] theorem byteStored_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (byteStored s) = r (.SFP reg) s := by
  simp [byteStored, storeMemory, NatCompare.saved, state_simp_rules]

end SszArm.Emit.Bits
