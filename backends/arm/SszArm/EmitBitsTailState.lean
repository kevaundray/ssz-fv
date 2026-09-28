import SszArm.EmitBitsMemory
import SszArm.EmitBitsMaskExec

namespace SszArm.Emit.Bits

open SszNative.Serialize (Desc Packed)
open Delimited (MemoryFrame)

theorem WorkRegisters.of_body_frame {s t : ArmState} {args : Args} {path : Path}
    {desc : Desc} {bits : Packed} {size : Nat}
    (work : WorkRegisters s args path bits) (owned : Owned s args desc (.bits bits) size)
    (frame : MemoryFrame (bodyWrites args size) s t)
    (same : ∀ reg : BitVec 5, reg ∉ [8#5, 9#5, 10#5] → r (.GPR reg) t = r (.GPR reg) s) :
    WorkRegisters t args path bits := by
  have fullFrame : MemoryFrame (writesFor args size) s t := by
    intro address outside
    exact frame address (fun span member => outside span (bodyWrites_subset args size span member))
  have header := frame_read_offset fullFrame args.value 48 16 8 owned.valueBound owned.valueOwned (by decide)
  refine ⟨(same _ (by decide)).trans work.result, (same _ (by decide)).trans work.output,
    (same _ (by decide)).trans work.capacity, (same _ (by decide)).trans work.stack,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact (same _ (by decide)).trans (work.source.trans header.symm)
  · rw [same _ (by decide)]; exact work.full
  · rw [same _ (by decide)]; exact work.backing
  · rw [same _ (by cases path <;> decide)]; exact work.low
  · intro isList; rw [same _ (by decide)]; exact work.remainder isList

theorem _root_.SszArm.Emit.Owned.of_body_frame {s t : ArmState} {args : Args} {desc : Desc}
    {bits : Packed} {size : Nat} (owned : Owned s args desc (.bits bits) size)
    (frame : MemoryFrame (bodyWrites args size) s t) : Owned t args desc (.bits bits) size := by
  apply owned.of_frame
  intro address outside
  exact frame address (fun span member => outside span (bodyWrites_subset args size span member))

theorem WorkRegisters.of_memory {s t : ArmState} {args : Args} {path : Path}
    {desc : Desc} {bits : Packed} {size : Nat}
    (work : WorkRegisters s args path bits) (owned : Owned s args desc (.bits bits) size)
    (memory : t.mem = s.mem)
    (same : ∀ reg : BitVec 5, reg ∉ [8#5, 9#5, 10#5] → r (.GPR reg) t = r (.GPR reg) s) :
    WorkRegisters t args path bits :=
  work.of_body_frame owned (fun address _ => congrFun memory address) same

def Path.indexStart : Path → Nat
  | .list => 664 | .vector => 1272

def Path.indexOp : Path → Tail.Op
  | .list => .p664 | .vector => .p1272

@[irreducible] def indexed (s : ArmState) : ArmState :=
  Activation.put 9 (r (.GPR 23#5) s + 1#64) s

theorem index_run (path : Path) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 path.indexStart) : run 1 s = indexed s := by
  have position : read_pc s = base + BitVec.ofNat 64 path.indexOp.row.1 := by cases path <;> exact pc
  change stepi s = _
  rw [Tail.step path.indexOp s base code error aligned position]
  unfold indexed
  cases path <;> rfl

@[simp] theorem indexed_pc (s : ArmState) : read_pc (indexed s) = read_pc s + 4#64 := by
  simp [indexed, Activation.put, Activation.next, state_simp_rules]

@[simp] theorem indexed_word (s : ArmState) : r (.GPR 9#5) (indexed s) = r (.GPR 23#5) s + 1#64 := by
  simp [indexed, Activation.put, Activation.next, state_simp_rules]

@[simp] theorem indexed_program (s : ArmState) : (indexed s).program = s.program := by
  simp [indexed, Activation.put, Activation.next, state_simp_rules]

@[simp] theorem indexed_error (s : ArmState) : read_err (indexed s) = read_err s := by
  simp [indexed, Activation.put, Activation.next, state_simp_rules]

@[simp] theorem indexed_memory (s : ArmState) : (indexed s).mem = s.mem := by
  simp [indexed, Activation.put, Activation.next, state_simp_rules]

@[simp] theorem indexed_register (s : ArmState) (reg : BitVec 5) (other : reg ≠ 9#5) :
    r (.GPR reg) (indexed s) = r (.GPR reg) s := by
  simp [indexed, Activation.put, Activation.next, state_simp_rules, other]

@[simp] theorem indexed_vector (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (indexed s) = r (.SFP reg) s := by
  simp [indexed, Activation.put, Activation.next, state_simp_rules]

@[irreducible] def listBranched (s : ArmState) (base : BitVec 64) (hasTail : Bool) : ArmState :=
  w .PC (base + if hasTail then 656#64 else 1484#64) s

theorem list_branch_run (s : ArmState) (base : BitVec 64) (args : Args) (bits : Packed)
    (work : WorkRegisters s args .list bits)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 652#64) :
    run 1 s = listBranched s base (decide (bits.count.toNat % 8 ≠ 0)) := by
  have remainder := work.remainder rfl
  have bounded : (r (.GPR 25#5) s).toNat < 8 := by omega
  have zero : (r (.GPR 25#5) s).setWidth 32 = 0#32 ↔ bits.count.toNat % 8 = 0 := by
    constructor
    · intro same; have := congrArg BitVec.toNat same
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
      omega
    · intro same
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
  change stepi s = _
  rw [Tail.step .p652 s base code error aligned pc]
  change r .PC s = _ at pc
  by_cases empty : bits.count.toNat % 8 = 0 <;>
    simp [Tail.Op.effect, Dispatch.branch, listBranched, zero, empty,
      state_simp_rules, pc, BitVec.add_assoc]

@[irreducible] def delimiterOne (s : ArmState) : ArmState := Activation.put 8 1#64 s

theorem delimiter_one_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1484#64) : run 1 s = delimiterOne s := by
  change stepi s = _
  rw [Tail.step .p1484 s base code error aligned pc]
  unfold delimiterOne
  rfl

end SszArm.Emit.Bits
