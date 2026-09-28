import SszArm.DispatchPrologue
import SszArm.DispatchTree

namespace SszArm.Dispatch

/-- Original entry descriptor tag and its separation from the six save pairs.
There is no future state, internal tag register, branch result, or body ownership
premise in this entry contract. -/
structure EntryOwned (s : ArmState) (kind : Kind) : Prop where
  stackLow : 368 ≤ (r (.GPR 31#5) s).toNat
  descriptorBound : (r (.GPR 1#5) s).toNat + 8 ≤ 2^64
  descriptorStack : (r (.GPR 1#5) s).toNat + 8 ≤ (r (.GPR 31#5) s).toNat - 96 ∨
    (r (.GPR 31#5) s).toNat ≤ (r (.GPR 1#5) s).toNat
  tag : read_mem_bytes 8 (r (.GPR 1#5) s) s = kind.tag

def entered (s : ArmState) (kind : Kind) : ArmState := selected (prologue s) kind

def Kind.steps (kind : Kind) : Nat := 7 + kind.ops.length

@[simp] theorem entered_program (s : ArmState) (kind : Kind) :
    (entered s kind).program = s.program := by simp [entered]

@[simp] theorem entered_error (s : ArmState) (kind : Kind) :
    read_err (entered s kind) = read_err s := by simp [entered]

@[simp] theorem entered_sp (s : ArmState) (kind : Kind) :
    r (.GPR 31#5) (entered s kind) = bodySP s := by simp [entered]

@[simp] theorem entered_reg (s : ArmState) (kind : Kind) (reg : BitVec 5)
    (notTag : reg ≠ 8#5) (notArena : reg ≠ 19#5) (notSP : reg ≠ 31#5) :
    r (.GPR reg) (entered s kind) = r (.GPR reg) s := by
  simp [entered, notTag, notArena, notSP]

@[simp] theorem entered_arena (s : ArmState) (kind : Kind) :
    r (.GPR 19#5) (entered s kind) = r (.GPR 4#5) s := by simp [entered]

@[simp] theorem entered_vector (s : ArmState) (kind : Kind) (reg : BitVec 5) :
    r (.SFP reg) (entered s kind) = r (.SFP reg) s := by simp [entered]

@[simp] theorem entered_memory (s : ArmState) (kind : Kind) :
    (entered s kind).mem = (prologue s).mem := by simp only [entered, selected_memory]

theorem entered_aligned (s : ArmState) (kind : Kind) (aligned : CheckSPAlignment s) :
    CheckSPAlignment (entered s kind) := selected_aligned _ _ (prologue_aligned s aligned)

theorem entered_frame (s : ArmState) (kind : Kind)
    (low : 368 ≤ (r (.GPR 31#5) s).toNat) (a : BitVec 64)
    (outside : a.toNat < (r (.GPR 31#5) s).toNat - 96 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat) :
    (entered s kind).mem a = s.mem a := by
  rw [entered_memory]
  exact prologue_frame s low a outside

theorem entered_read (s : ArmState) (kind : Kind)
    (low : 368 ≤ (r (.GPR 31#5) s).toNat) (address : BitVec 64) (bytes : Nat)
    (bound : address.toNat + bytes ≤ 2^64)
    (outside : address.toNat + bytes ≤ (r (.GPR 31#5) s).toNat - 96 ∨
      (r (.GPR 31#5) s).toNat ≤ address.toNat) :
    read_mem_bytes bytes address (entered s kind) = read_mem_bytes bytes address s := by
  apply BoolCodec.read_bytes_congr
  intro i hi
  apply entered_frame s kind low
  bv_omega

theorem entered_saved (s : ArmState) (kind : Kind)
    (low : 368 ≤ (r (.GPR 31#5) s).toNat) (reg : BitVec 5) (offset : Nat)
    (member : (reg, offset) ∈ BoolCodec.savedRegisters) :
    read_mem_bytes 8 (bodySP s + BitVec.ofNat 64 offset) (entered s kind) = r (.GPR reg) s := by
  have memory : read_mem_bytes 8 (bodySP s + BitVec.ofNat 64 offset) (entered s kind) =
      read_mem_bytes 8 (bodySP s + BitVec.ofNat 64 offset) (prologue s) := by
    apply BoolCodec.read_bytes_congr
    intro i hi
    exact congrFun (entered_memory s kind) _
  exact memory.trans (prologue_saved s low reg offset member)

theorem prologue_tag {s : ArmState} {kind : Kind} (owned : EntryOwned s kind) :
    read_mem_bytes 8 (r (.GPR 1#5) (prologue s)) (prologue s) = kind.tag := by
  rw [prologue_reg s 1#5 (by decide)]
  rw [← owned.tag]
  apply BoolCodec.read_bytes_congr
  intro i hi
  apply prologue_frame s owned.stackLow
  have bound := owned.descriptorBound
  have outside := owned.descriptorStack
  bv_omega

theorem entered_pc (s : ArmState) (base : BitVec 64) (kind : Kind)
    (owned : EntryOwned s kind) (pc : read_pc s = base) :
    read_pc (entered s kind) = base + BitVec.ofNat 64 kind.entry := by
  apply selected_pc
  · simpa only [prologue_pc, pc]
  · exact prologue_tag owned

/-- Actual private function entry, all save stores, descriptor load, signed CMP
branch tree, and the exact accepted body PC. -/
theorem entry_run (s : ArmState) (base : BitVec 64) (kind : Kind)
    (owned : EntryOwned s kind) (code : CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    run kind.steps s = entered s kind := by
  rw [Kind.steps, run_plus, prologue_run s base code error aligned pc]
  apply selected_run _ base kind
  · simpa only [CodeAt, prologue_program] using code
  · simpa only [prologue_error] using error
  · exact prologue_aligned s aligned
  · simpa only [prologue_pc, pc]
  · exact prologue_tag owned

end SszArm.Dispatch
