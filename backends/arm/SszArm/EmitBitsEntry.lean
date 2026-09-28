import SszArm.EmitBitsQuotient
import SszArm.EmitObservations

namespace SszArm.Emit.Bits

open SszNative.Serialize (Desc Packed)
open Delimited (MemoryFrame)

def dispatchOps : List Op := [.p568, .p572, .p576]

@[irreducible] def dispatched (s : ArmState) : ArmState := block dispatchOps s

def countEntry : Desc → Nat
  | .bitVector _ => 1180
  | _ => 580

theorem dispatch_follows (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 568#64) :
    Follows base dispatchOps s := by
  change r .PC s = _ at pc
  simp (config := {decide := true, instances := true})
    [Follows, dispatchOps, Op.row, Op.effect, Activation.put, Activation.next,
     Dispatch.next, Dispatch.compare64, Dispatch.branch, state_simp_rules,
     aligned, CheckSPAlignment, pc, BitVec.add_assoc]
  exact BoolCodec.stack_aligned s aligned

theorem dispatch_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 568#64) : run 3 s = dispatched s := by
  rw [dispatched]
  exact runs dispatchOps s base code error (dispatch_follows s base aligned pc)

theorem dispatched_pc (s : ArmState) (base : BitVec 64) (desc : Desc)
    (kind : IsBits desc) (pc : read_pc s = base + 568#64)
    (tag : r (.GPR 8#5) s = descriptorTag desc) :
    read_pc (dispatched s) = base + BitVec.ofNat 64 (countEntry desc) := by
  change r .PC s = _ at pc
  cases desc <;> try cases kind
  all_goals
    simp (config := {decide := true, instances := true})
      [dispatched, block, dispatchOps, Op.effect, countEntry,
       Activation.put, Activation.next, Dispatch.next, Dispatch.compare64,
       Dispatch.branch, state_simp_rules, bitvec_rules, minimal_theory,
       pc, tag, descriptorTag, BitVec.add_assoc]

@[simp] theorem dispatched_program (s : ArmState) : (dispatched s).program = s.program := by
  simp [dispatched, block, dispatchOps]

@[simp] theorem dispatched_error (s : ArmState) : read_err (dispatched s) = read_err s := by
  simp [dispatched, block, dispatchOps]

@[simp] theorem dispatched_memory (s : ArmState) : (dispatched s).mem = s.mem := by
  simp [dispatched, block, dispatchOps, Op.effect, Activation.put, Activation.next,
    Dispatch.next, Dispatch.compare64, Dispatch.branch, state_simp_rules]

@[simp] theorem dispatched_register (s : ArmState) (reg : BitVec 5) (other : reg ≠ 9#5) :
    r (.GPR reg) (dispatched s) = r (.GPR reg) s := by
  simp [dispatched, block, dispatchOps, Op.effect, Activation.put, Activation.next,
    Dispatch.next, Dispatch.compare64, Dispatch.branch, state_simp_rules, other]

@[simp] theorem dispatched_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (dispatched s) = r (.SFP reg) s := by
  simp [dispatched, block, dispatchOps, Op.effect, Activation.put, Activation.next,
    Dispatch.next, Dispatch.compare64, Dispatch.branch, state_simp_rules]

theorem shifted_frame (path : Path) (s : ArmState) (args : Args) (size : Nat)
    (stack : r (.GPR 31#5) s = args.bodySP) (low : 176 ≤ args.stack.toNat) :
    MemoryFrame (bodyWrites args size) s (shifted path s) := by
  have address : (r (.GPR 31#5) s - 16#64).toNat = args.stack.toNat - 176 := by
    rw [stack, Args.bodySP]
    bv_omega
  have stackBound := args.stack.isLt
  intro a outside
  have away := outside (args.stack.toNat - 176, 16) (by simp [bodyWrites])
  have stored := BoolCodec.write_mem_bytes_frame s (r (.GPR 31#5) s - 16#64) 8
    (r (.GPR 9#5) s) a (by rw [address]; omega) (by rw [address]; omega)
  simpa [shifted, NatCompare.saved, state_simp_rules] using stored

theorem shifted_owned (path : Path) {s : ArmState} {args : Args} {desc : Desc}
    {bits : Packed} {size : Nat} (owned : Owned s args desc (.bits bits) size)
    (stack : r (.GPR 31#5) s = args.bodySP) :
    Owned (shifted path s) args desc (.bits bits) size := by
  apply owned.of_frame
  intro address outside
  exact shifted_frame path s args size stack owned.stackLow address
    (fun span member => outside span (bodyWrites_subset args size span member))

end SszArm.Emit.Bits
